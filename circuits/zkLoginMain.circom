pragma circom 2.1.3;

include "helpers/sha256.circom";
include "helpers/misc.circom";
include "helpers/strings.circom";
include "helpers/hasher.circom";
include "helpers/jwtchecks.circom";
include "helpers/rsa/rsa.circom";

/**
zkLogin circuit

Terminology: An "unsigned JWT" is a byte array of the form: header || '.' || payload.
    In other words, it is nothing but the JWT without the signature.
Similarly, a "padded unsigned JWT" is of the form: header || '.' || payload || sha2pad || zeroes (optional).

Constraints (dominant terms, rough):
    - (maxPaddedUnsignedJWTLen / 64) * 30k [SHA2_wrapper]
    - 155k [RSA]
    - (128 + maxPaddedUnsignedJWTLen/32) * (maxExtKCLen + maxExtNonceLength + maxExtEVLength) [ASCIISubstrExistsInB64]

Construction params:
    - maxHeaderLen:             Maximum length of the JWT header (in bytes)
    - maxPaddedUnsignedJWTLen:  Maximum length of the padded unsigned JWT. Must be a multiple of 64.
    - maxKCNameLen:             Maximum length of the key_claim_name (in bytes)
    - maxKCValueLen:            Maximum length of the key_claim_value (in bytes)
    - maxAudValueLen:           Maximum length of aud (in bytes)
    - maxWhiteSpaceLen:         The number of JSON whitespaces that we can tolerate in an extended claim
    - maxExtIssLength:          Maximum length the extended iss claim (in ASCII bytes)

Private Inputs:
    - padded_unsigned_jwt[inCount]: X in bytes where X is the padded unsigned JWT + zeroes
    - payload_start_index:      The index of the first byte of the payload in the padded unsigned JWT

    - num_sha2_blocks:          The number of SHA2 blocks in the padded unsigned JWT
    - payload_len:              The length of the payload

    - signature:                The signature of the JWT (little endian)
    - modulus:                  The modulus of the RSA public key (little endian)

    - ext_kc[maxExtKCLen]:
                                The extended key claim padded by 0s
    - ext_kc_length:            Length of ext_kc in ASCII, e.g., for ',"sub":12345,' it is 13
    - kc_index_b64, kc_length_b64:
                                The index and length of ext_kc (encoded into Base64) in the JWT payload
    - kc_name_length, kc_colon_index, kc_value_index, kc_value_length
                                The various indices and lengths of the extended_key_claim to facilitate parsing

    - ext_nonce[maxNonceLength]: The extended nonce claim
    - ext_nonce_length, nonce_index_b64, nonce_length_b64, nonce_colon_index, nonce_value_index
    - eph_public_key[2]:        The ephemeral public key split into two 128-bit values
    - max_epoch:                The maximum epoch for which the eph_public_key is valid
    - jwt_randomness:           A 128-bit random number to keep the sensitive parts of JWT hidden.

    - ext_ev[maxExtEVLength]:   The extended email_verified claim
    - ext_ev_length, ev_index_b64, ev_length_b64, ev_name_length, ev_colon_index, ev_value_index, ev_value_length

    - iss_index_b64:            The start index of the iss in the padded unsigned JWT
    - iss_length_b64:           The length of the iss in the padded unsigned JWT

    - salt:                     The subject's salt

Signals revealed to the verifier along with the ZK proof:
    - eph_public_key, max_epoch, address_seed
    - iss_b64:                  The base64-encoded extended iss
    - iss_index_in_payload_mod_4: The start index mod 4 of the position at which iss_b64 appears
    - header, modulus

Public Inputs:
    - all_inputs_hash:          Hash of all the signals revealed to the verifier

Note: The circuit does not restrict the key claim names intentionally.
This is not a security issue because the key claim name (e.g., "sub") 
is used to derive a user's address seed. So using a different key 
claim name will just result in a different address.
*/
template zkLogin(maxHeaderLen, maxPaddedUnsignedJWTLen,
                 maxKCNameLen, maxKCValueLen, maxExtKCLen,
                 maxAudValueLen, maxWhiteSpaceLen, maxExtIssLength) {
    var inWidth = 8; // input is in bytes
    var inCount = maxPaddedUnsignedJWTLen;

    /**
     1. Parse out the JWT header 
    **/
    signal input padded_unsigned_jwt[inCount];
    signal input payload_start_index;

    // Extract the header
    var header_length = payload_start_index - 1;
    signal header[maxHeaderLen] <== SliceFromStart(inCount, maxHeaderLen)(
        padded_unsigned_jwt, header_length
    );
    signal header_F <== HashBytesToField(maxHeaderLen)(header);

    // Check that there is a dot after header
    var x = SingleMultiplexer(inCount)(padded_unsigned_jwt, header_length);
    x === 46; // 46 is the ASCII code for '.'

    /**
     2. SHA2 operations over padded_unsigned_jwt
        - Check the validity of SHA2 padding
        - Compute SHA2(padded_unsigned_jwt)
    */
    signal input num_sha2_blocks;
    signal input payload_len;

    // Check the validity of the SHA2 padding
    var padded_unsigned_jwt_len = 64 * num_sha2_blocks; // 64 bytes per SHA2 block
    var sha2pad_index = payload_start_index + payload_len;
    SHA2PadVerifier(inCount)(padded_unsigned_jwt, padded_unsigned_jwt_len, sha2pad_index);

    var hashCount = 4;
    var hashWidth = 256 / hashCount;
    signal jwt_sha2_hash[hashCount] <== Sha2_wrapper(inWidth, inCount, hashWidth, hashCount)(
        padded_unsigned_jwt, num_sha2_blocks
    );

    /**
     3. Check signature
    **/
    signal input signature[32]; // The JWT signature  
    signal input modulus[32];
    var jwt_sha2_hash_le[4]; // converting to little endian
    for (var i = 0; i < 4; i++) {
        jwt_sha2_hash_le[i] = jwt_sha2_hash[3 - i];
    }
    RSAVerify65537()(signature, modulus, jwt_sha2_hash_le);

    // HashToField for revealing modulus
    var modulus_be[32]; // converting to big endian
    for (var i = 0; i < 32; i++) {
        modulus_be[i] = modulus[31 - i];
    }
    signal modulus_F <== HashToField(64, 32)(modulus_be);

    /**
     4. Checks on extended_key_claim + extract key claim name, value

    Note that the OpenID standard permits extended_key_claim to be any valid JSON member. 
    But the below logic is (slightly) more restrictive as it imposes a few length restrictions:
        - the extended claim needs to fit in maxExtKCLen bytes
        - the claim name needs to fit in maxKCNameLen bytes
        - the claim value needs to fit in maxKCValueLen bytes
    */

    var subInWidth = 8;
    var maxKCNameLenWithQuotes = maxKCNameLen + 2; // 2 for quotes
    var maxKCValueLenWithQuotes = maxKCValueLen + 2; // 2 for quotes
    // 1 for colon, 1 for comma / brace

    // We set maxExtKCLen to a value lesser than 
    //  maxKCNameLenWithQuotes + maxKCValueLenWithQuotes + 2 + maxWhiteSpaceLen
    //  as we optimize #constraints. See the comments section in ExtClaimOps for more details.
    signal input ext_kc[maxExtKCLen];
    signal input ext_kc_length;
    signal input kc_index_b64;
    signal input kc_length_b64;
    signal input kc_name_length; // with quotes
    signal input kc_colon_index;
    signal input kc_value_index;
    signal input kc_value_length; // with quotes

    signal kc_name_with_quotes[maxKCNameLenWithQuotes];
    signal kc_value_with_quotes[maxKCValueLenWithQuotes];

    component KCExtClaim = ExtClaimOps(
        inCount, maxExtKCLen, maxKCNameLenWithQuotes, maxKCValueLenWithQuotes, maxWhiteSpaceLen
    );

    KCExtClaim.content <== padded_unsigned_jwt;
    KCExtClaim.index_b64 <== kc_index_b64;
    KCExtClaim.length_b64 <== kc_length_b64;
    KCExtClaim.ext_claim <== ext_kc;
    KCExtClaim.ext_claim_length <== ext_kc_length;
    KCExtClaim.name_length <== kc_name_length;
    KCExtClaim.colon_index <== kc_colon_index;
    KCExtClaim.value_index <== kc_value_index;
    KCExtClaim.value_length <== kc_value_length;
    KCExtClaim.payload_start_index <== payload_start_index;

    kc_name_with_quotes <== KCExtClaim.claim_name;
    kc_value_with_quotes <== KCExtClaim.claim_value;

    // HashBytesToField for later use
    signal kc_name[maxKCNameLen] <== QuoteRemover(maxKCNameLen + 2)(
        kc_name_with_quotes, kc_name_length
    );
    signal kc_name_F <== HashBytesToField(maxKCNameLen)(kc_name);

    signal kc_value[maxKCValueLen] <== QuoteRemover(maxKCValueLen + 2)(
        kc_value_with_quotes, kc_value_length
    );
    signal kc_value_F <== HashBytesToField(maxKCValueLen)(kc_value);

    /**
     5. Checks on extended_nonce
        a) Is it in the JWT payload? 
        b) Calculate nonce from public key, epoch, and randomness
        c) Check that nonce appears in extended_nonce
    **/
    var nonce_name_length = 7;
    var nonce_value_length = 29; // 27 for Base64 encoding of 256 bits, 2 for quotes
    var maxExtNonceLength = nonce_name_length + nonce_value_length + 2 + maxWhiteSpaceLen;

    signal input ext_nonce[maxExtNonceLength];
    signal input ext_nonce_length;
    signal input nonce_index_b64;
    signal input nonce_length_b64;
    signal input nonce_colon_index;
    signal input nonce_value_index;

    signal nonce_name_with_quotes[nonce_name_length];
    signal nonce_value_with_quotes[nonce_value_length];

    component NonceExtClaim = ExtClaimOps(
        inCount, maxExtNonceLength, nonce_name_length, nonce_value_length, maxWhiteSpaceLen
    );
    NonceExtClaim.content <== padded_unsigned_jwt;
    NonceExtClaim.index_b64 <== nonce_index_b64;
    NonceExtClaim.length_b64 <== nonce_length_b64;
    NonceExtClaim.ext_claim <== ext_nonce;
    NonceExtClaim.ext_claim_length <== ext_nonce_length;
    NonceExtClaim.name_length <== nonce_name_length;
    NonceExtClaim.colon_index <== nonce_colon_index;
    NonceExtClaim.value_index <== nonce_value_index;
    NonceExtClaim.value_length <== nonce_value_length;
    NonceExtClaim.payload_start_index <== payload_start_index;

    nonce_name_with_quotes <== NonceExtClaim.claim_name;
    nonce_value_with_quotes <== NonceExtClaim.claim_value;

    var expected_nonce_name[nonce_name_length] = [34, 110, 111, 110, 99, 101, 34]; // "nonce"
    for (var i = 0; i < nonce_name_length; i++) {
        nonce_name_with_quotes[i] === expected_nonce_name[i];
    }

    // 5b) Calculate nonce
    signal input eph_public_key[2];
    signal input max_epoch;
    signal input jwt_randomness;
    component size_checker_2 = Num2Bits(128);
    size_checker_2.in <== jwt_randomness; // ensure it is 16 bytes

    signal nonce <== Hasher(4)([
        eph_public_key[0],
        eph_public_key[1],
        max_epoch,
        jwt_randomness
    ]);

    // 5c) Check that nonce appears in extended_nonce
    NonceChecker(nonce_value_length, 160)(
        expected_nonce <== nonce,
        actual_nonce <== nonce_value_with_quotes
    );

    /**
    6. Checks on the email_verified claim:
        If the key claim is email, then we check that the value is true.
        Otherwise, it is expected that the nonce string is input so that string parsing routines do not complain.
    **/

    var maxEVNameLenWithQuotes = 16; // 2 for quotes
    var maxEVValueLen = 29; // same as nonce
    var maxExtEVLength = maxEVNameLenWithQuotes + maxEVValueLen + 2 + maxWhiteSpaceLen;

    signal input ext_ev[maxExtEVLength];
    signal input ext_ev_length;
    signal input ev_index_b64;
    signal input ev_length_b64;
    signal input ev_name_length;
    signal input ev_colon_index;
    signal input ev_value_index;
    signal input ev_value_length;

    signal ev_name_with_quotes[maxEVNameLenWithQuotes];
    signal ev_value[maxEVValueLen];
    component EVExtClaim = ExtClaimOps(
        inCount, maxExtEVLength, maxEVNameLenWithQuotes, maxEVValueLen, maxWhiteSpaceLen
    );
    EVExtClaim.content <== padded_unsigned_jwt;
    EVExtClaim.index_b64 <== ev_index_b64;
    EVExtClaim.length_b64 <== ev_length_b64;
    EVExtClaim.ext_claim <== ext_ev;
    EVExtClaim.ext_claim_length <== ext_ev_length;
    EVExtClaim.name_length <== ev_name_length;
    EVExtClaim.colon_index <== ev_colon_index;
    EVExtClaim.value_index <== ev_value_index;
    EVExtClaim.value_length <== ev_value_length;
    EVExtClaim.payload_start_index <== payload_start_index;

    ev_name_with_quotes <== EVExtClaim.claim_name;
    ev_value <== EVExtClaim.claim_value;

    EmailVerifiedChecker(maxKCNameLen, maxEVValueLen)(
        kc_name, kc_name_length - 2, // -2 for quotes
        ev_name_with_quotes, ev_value, ev_value_length
    );

    /**
    7. Checks on ext_aud + extract aud
    **/

    var aud_name_length = 3 + 2; // "aud"
    var maxAudValueLenWithQuotes = maxAudValueLen + 2; // 2 for quotes
    // 1 for colon, 1 for comma / brace
    var maxExtAudLength = aud_name_length + maxAudValueLenWithQuotes + 2 + maxWhiteSpaceLen;
    signal input ext_aud[maxExtAudLength];
    signal input ext_aud_length;
    signal input aud_index_b64;
    signal input aud_length_b64;
    signal input aud_colon_index;
    signal input aud_value_index;
    signal input aud_value_length; // with quotes
    signal aud_name_with_quotes[aud_name_length];
    signal aud_value_with_quotes[maxAudValueLenWithQuotes];

    component AudExtClaim = ExtClaimOps(
        inCount, maxExtAudLength, aud_name_length, maxAudValueLenWithQuotes, maxWhiteSpaceLen
    );
    AudExtClaim.content <== padded_unsigned_jwt;
    AudExtClaim.index_b64 <== aud_index_b64;
    AudExtClaim.length_b64 <== aud_length_b64;
    AudExtClaim.ext_claim <== ext_aud;
    AudExtClaim.ext_claim_length <== ext_aud_length;
    AudExtClaim.name_length <== aud_name_length;
    AudExtClaim.colon_index <== aud_colon_index;
    AudExtClaim.value_index <== aud_value_index;
    AudExtClaim.value_length <== aud_value_length;
    AudExtClaim.payload_start_index <== payload_start_index;

    aud_name_with_quotes <== AudExtClaim.claim_name;
    aud_value_with_quotes <== AudExtClaim.claim_value;

    // Check if aud_name_with_quotes == "aud"
    var expected_aud_name[aud_name_length] = [34, 97, 117, 100, 34];
    for (var i = 0; i < aud_name_length; i++) {
        aud_name_with_quotes[i] === expected_aud_name[i];
    }

    // HashBytesToField for later use
    signal aud_value[maxAudValueLen] <== QuoteRemover(maxAudValueLen + 2)(
        aud_value_with_quotes, aud_value_length
    );
    signal aud_value_F <== HashBytesToField(maxAudValueLen)(aud_value);

    /**
    8. Reveal the portion of JWT encoding the extended iss claim.
       Note that we are revealing a base64 string.
    **/
    signal input iss_index_b64;
    signal input iss_length_b64;
    var iss_b64_F; // output
    var iss_index_in_payload_mod_4; // output

    var maxExtIssLength_b64 = 4 * (1 + (maxExtIssLength \ 3)); // max(b64Len(maxA, i)) for any i
    var iss_b64[maxExtIssLength_b64] = SliceEfficient(inCount, maxExtIssLength_b64)(
        padded_unsigned_jwt, iss_index_b64, iss_length_b64
    );

    // HashBytesToField for all inputs hash
    iss_b64_F = HashBytesToField(maxExtIssLength_b64)(iss_b64);
    iss_index_in_payload_mod_4 = RemainderMod4(numBits(inCount))(iss_index_b64 - payload_start_index);

    /**
    9. Compute the address seed
    **/
    signal input salt;
    signal hashed_salt <== Hasher(1)([salt]);
    signal address_seed <== Hasher(4)([
        kc_name_F, kc_value_F, aud_value_F, hashed_salt
    ]);

    /**
    10. Compress public inputs
        We reveal a hash of some signals to the verifier. These signal values
        need to be given to the verifier along with ZK proof.
    **/
    signal input all_inputs_hash;
    signal all_inputs_hash_actual <== Hasher(8)([
        eph_public_key[0],
        eph_public_key[1],
        address_seed,
        max_epoch,
        iss_b64_F,
        iss_index_in_payload_mod_4,
        header_F,
        modulus_F
    ]);
    all_inputs_hash === all_inputs_hash_actual;
}
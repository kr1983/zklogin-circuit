pragma circom 2.1.3;

include "../../node_modules/circomlib/circuits/aliascheck.circom";
include "../../node_modules/circomlib/circuits/comparators.circom";
include "../../node_modules/circomlib/circuits/gates.circom";

include "hasher.circom";
include "misc.circom";
include "strings.circom";

/**
ExtClaimOps
1. Check if the extended claim appears as a substring in the Base64-encoded JWT payload
2. Extract the claim name and value from the extended claim

Note that the extracted claim name and value might include quotes if the
    underlying thing is a JSON string.

Construction params:
- inCount:              Maximum length of the JWT payload
- maxExtClaimLen:       Maximum length of the extended claim
- maxClaimNameLen:      Maximum length of the claim name (including quotes)
- maxClaimValueLen:     Maximum length of the claim value (including quotes)
- maxWhiteSpaceLen:     Maximum number of white space characters

Ideally, we want to set 
maxExtClaimLen = maxClaimNameLen + maxClaimValueLen + maxWhiteSpaceLen + 2 (2 for colon, comma).
But in some cases (e.g., maxExtKCLen), we set it to a value lesser than that (to reduce #constraints).
It just implies that the circuit will not be able to handle a situation where the 
claim name is maxClaimNameLen, claim value is maxClaimValueLen and there are maxWhiteSpaceLen whitespaces.
**/
template ExtClaimOps(inCount, maxExtClaimLen, maxClaimNameLen, maxClaimValueLen, maxWhiteSpaceLen) {
    signal input content[inCount];
    signal input index_b64;
    signal input length_b64;

    signal input ext_claim[maxExtClaimLen];
    signal input ext_claim_length;
    signal input name_length; // with quotes
    signal input colon_index;
    signal input value_index;
    signal input value_length; // with quotes

    signal input payload_start_index;

    ASCIISubstrExistsInB64(
        inCount, maxExtClaimLen
    )(
        b64Str <== content,
        BIndex <== index_b64,
        lenB <== length_b64,
        A <== ext_claim,
        lenA <== ext_claim_length,
        payloadIndex <== payload_start_index
    );

    signal output claim_name[maxClaimNameLen];
    signal output claim_value[maxClaimValueLen];

    (claim_name, claim_value) <== ExtendedClaimParser(
        maxExtClaimLen, maxClaimNameLen, maxClaimValueLen
    )(
        ext_claim, ext_claim_length,
        name_length, colon_index, value_index, value_length
    );
}

/**
ExtendedClaimParser

string ws : ws value ws E
     |    |    |   |    |
     n    ci   vi  ve   l => n = name_length, ci = ':', v = value_index, ve = value_end, l = ext_claim_length

Construction Params:
    - maxExtendedClaimLen: maximum length of the extended claim string
    - maxClaimNameLen: maximum length of the key claim name (including quotes)
    - maxClaimValueLen: maximum length of the key claim value (including quotes)

Range checks:
    - 0 < ext_claim_length (LTBitVector) and ext_claim_length <= maxExtendedClaimLen (this)
    - 0 < name_length <= maxClaimNameLen (SliceFromStart)
    - 0 < value_length <= maxClaimValueLen (SliceEfficient)
    - 0 < colon_index < maxExtendedClaimLen
    - 0 < value_index, value_index + value_length <= maxExtendedClaimLen
    - name_length <= colon_index < value_index

Note that we do not perform all the checks that a JSON-coforming parser would do.
    For example, we do not check if the claim name or value is a valid JSON string.
**/
template ExtendedClaimParser(maxExtendedClaimLen, maxClaimNameLen, maxClaimValueLen) {
    assert(maxExtendedClaimLen > 0);
    assert(maxClaimNameLen > 0);
    assert(maxClaimValueLen > 0);

    signal input extended_claim[maxExtendedClaimLen];
    signal input ext_claim_length;
    RangeCheck(numBits(maxExtendedClaimLen), maxExtendedClaimLen)(ext_claim_length);

    signal input name_length;
    signal input colon_index;
    signal input value_index;
    signal input value_length;

    var x = LessEqThan(numBits(maxExtendedClaimLen))([name_length, colon_index]);
    x === 1;
    x = LessThan(numBits(maxExtendedClaimLen))([colon_index, value_index]);
    x === 1;

    signal output name[maxClaimNameLen] <== SliceFromStart(maxExtendedClaimLen, maxClaimNameLen)(
        extended_claim, name_length
    );

    signal output value[maxClaimValueLen] <== SliceEfficient(maxExtendedClaimLen, maxClaimValueLen)(
        extended_claim, value_index, value_length
    );

    // Whitespaces
    signal is_whitespace[maxExtendedClaimLen];
    for (var i = 0; i < maxExtendedClaimLen; i++) {
        is_whitespace[i] <== isWhitespace()(extended_claim[i]);
    }

    signal is_gt_n[maxExtendedClaimLen] <== GTBitVector(maxExtendedClaimLen)(name_length - 1);
    signal is_lt_c[maxExtendedClaimLen] <== LTBitVector(maxExtendedClaimLen)(colon_index);
    signal selector1[maxExtendedClaimLen] <== vectorAND(maxExtendedClaimLen)(is_gt_n, is_lt_c);
    for (var i = 0; i < maxExtendedClaimLen; i++) {
        selector1[i] * (1 - is_whitespace[i]) === 0;
    }

    signal is_gt_c[maxExtendedClaimLen] <== GTBitVector(maxExtendedClaimLen)(colon_index);
    signal is_lt_vs[maxExtendedClaimLen] <== LTBitVector(maxExtendedClaimLen)(value_index);
    signal selector2[maxExtendedClaimLen] <== vectorAND(maxExtendedClaimLen)(is_gt_c, is_lt_vs);
    for (var i = 0; i < maxExtendedClaimLen; i++) {
        selector2[i] * (1 - is_whitespace[i]) === 0;
    }

    signal is_gt_ve[maxExtendedClaimLen] <== GTBitVector(maxExtendedClaimLen)(value_index + value_length - 1);
    signal is_lt_l[maxExtendedClaimLen] <== LTBitVector(maxExtendedClaimLen)(ext_claim_length - 1);

    // selector3[i] = is_gt_ve[i] * is_lt_l[i]
    signal selector3[maxExtendedClaimLen] <== vectorAND(maxExtendedClaimLen)(is_gt_ve, is_lt_l);
    for (var i = 0; i < maxExtendedClaimLen; i++) {
        selector3[i] * (1 - is_whitespace[i]) === 0;
    }

    // Colon is at index colon_index
    signal colon <== SingleMultiplexer(maxExtendedClaimLen)(extended_claim, colon_index);
    colon === 58; // ':'

    // Last char is either end-brace or comma
    signal last_char <== SingleMultiplexer(maxExtendedClaimLen)(extended_claim, ext_claim_length - 1);
    (last_char - 125) * (last_char - 44) === 0; // '}' or ','

    // Check that everything after is zero. (Not needed for safety, but just to be extra-cautious)
    signal is_gt_l[maxExtendedClaimLen] <== GTBitVector(maxExtendedClaimLen)(ext_claim_length - 1);
    for (var i = 0; i < maxExtendedClaimLen; i++) {
        is_gt_l[i] * extended_claim[i] === 0;
    }
}

/**
QuoteRemover
1. Checks if the string has quotes at the start and end.
2. Removes the quotes from the start and end and returns the raw string.

Range checks:
    - length in (0, inLen]
**/
template QuoteRemover(inLen) {
    assert(inLen >= 2);

    signal input in[inLen];
    signal input length;

    // first char is a quote
    in[0] === 34; // '"'

    // Remove the first quote
    var intermediate[inLen - 1];
    for (var i = 0; i < inLen - 1; i++) {
        intermediate[i] = in[i + 1];
    }

    // Remove the last quote
    signal output out[inLen - 2] <== SliceFromStart(inLen - 1, inLen - 2)(intermediate, length - 2);

    signal last_quote <== SingleMultiplexer(inLen)(in, length - 1); // 0 <= length - 1 < inLen
    last_quote === 34; // '"'
}

/**
isWhitespace: Checks if a character is whitespace (as defined by the JSON spec).

Outputs 1 if it is a whitespace character and 0 otherwise.
**/
template isWhitespace() {
    signal input c;

    signal is_space <== IsEqual()([c, 0x20]); // 0x20 = decimal 32
    signal is_tab <== IsEqual()([c, 0x09]); // 0x09 = decimal 9
    signal is_newline <== IsEqual()([c, 0x0A]); // 0x0A = decimal 10
    signal is_carriage_return <== IsEqual()([c, 0x0D]); // 0x0D = decimal 13

    signal output is_whitespace <== is_space + is_tab + is_newline + is_carriage_return;
}

/**
NonceChecker: Checks that the actual nonce extracted from the JWT matches the expected nonce.

Construction Params:
    nonceValueLength: length of the actual nonce value
    nonceBitLen: length of the nonce in bits

Inputs:
    expected_nonce: The expected nonce (Field element)
    actual_nonce: The Base64 encoded nonce with quotes
                    e.g, actual_nonce = '"Ac2SElwUoYv8jKhE6vs6Vmepu2M"'
                    Length of actual_nonce is nonceValueLength

The circuit checks if the least significant nonceBitLen bits of 
    expected_nonce match the Base64-decoded expected nonce.
**/
template NonceChecker(nonceValueLength, nonceBitLen) {
    assert(nonceValueLength > 0);
    assert(nonceBitLen > 0);

    signal input expected_nonce;
    signal expected_bits[254] <== Num2Bits_strict()(expected_nonce);

    signal input actual_nonce[nonceValueLength];

    // Remove the first and last character to get the actual nonce
    var nonceLength = nonceValueLength - 2;
    var value[nonceLength] = QuoteRemover(nonceValueLength)(actual_nonce, nonceValueLength);

    // Convert the base64url encoded nonce to bits
    signal actual_bits[6 * nonceLength] <== StrictDecodeB64String(nonceLength)(value);

    // Check every bit of expected nonce against the actual nonce
    // reverse(expected_bits[0:nonceBitLen]) == actual_bits[0:nonceBitLen]
    assert(6 * nonceLength >= nonceBitLen);
    for (var i = 0; i < nonceBitLen; i++) {
        expected_bits[nonceBitLen - i - 1] === actual_bits[i];
    }
}

/**
EmailVerifiedChecker: Checks if email_verified is true when the key claim is email.

Accepts both boolean true and string "true" as valid values for email_verified.
**/
template EmailVerifiedChecker(maxKCNameLen, maxEVValueLen) {
    assert(maxKCNameLen >= 5);
    assert(maxEVValueLen >= 4);

    signal input kc_name[maxKCNameLen];
    signal input kc_name_length;

    signal input ev_name_with_quotes[16]; // same as maxEVNameLenWithQuotes

    signal input ev_value[maxEVValueLen];
    signal input ev_value_length;

    // A simple way of checking if kc_name[0:kc_name_length] is indeed 'email'. 
    //   1. check if the first 5 characters are 'email'.
    //   2. check if the length is 5.
    var email[5] = [101, 109, 97, 105, 108];
    var is_email_0 = IsEqual()([kc_name[0], email[0]]);
    var is_email_1 = IsEqual()([kc_name[1], email[1]]);
    var is_email_2 = IsEqual()([kc_name[2], email[2]]);
    var is_email_3 = IsEqual()([kc_name[3], email[3]]);
    var is_email_4 = IsEqual()([kc_name[4], email[4]]);
    var is_email = MultiAND(5)([is_email_0, is_email_1, is_email_2, is_email_3, is_email_4]);

    AssertEqualIfEnabled()(is_email, [kc_name_length, 5]);

    var expected_ev_name[16] = [34, 101, 109, 97, 105, 108, 95, 118, 101, 114, 105, 102, 105, 101, 100, 34]; // "email_verified"
    for (var i = 0; i < 16; i++) {
        AssertEqualIfEnabled()(is_email, [ev_name_with_quotes[i], expected_ev_name[i]]);
    }

    var X = IsEqual()([ev_value_length, 4]);
    var Y = IsEqual()([ev_value_length, 6]);
    var Z = OR()(X, Y);
    AssertEqualIfEnabled()(is_email, [Z, 1]);

    var expecting_boolean_email = is_email * X;
    var expected_ev_value_boolean[4] = [116, 114, 117, 101]; // true
    for (var i = 0; i < 4; i++) {
        AssertEqualIfEnabled()(expecting_boolean_email, [ev_value[i], expected_ev_value_boolean[i]]);
    }

    var expecting_string_email = is_email * Y;
    var expected_ev_value_string[6] = [34, 116, 114, 117, 101, 34]; // "true"
    for (var i = 0; i < 6; i++) {
        AssertEqualIfEnabled()(expecting_string_email, [ev_value[i], expected_ev_value_string[i]]);
    }
}

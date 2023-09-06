pragma circom 2.1.3;

include "misc.circom";

function asciiToBase64UrlIndex(i) {
    var base64 = 64; // Invalid base64url character
    if (i >= 65 && i <= 90) { // A to Z
        base64 = i - 65;
    } else if (i >= 97 && i <= 122) { // a to z
        base64 = i - 71;
    } else if (i >= 48 && i <= 57) { // 0 to 9
        base64 = i + 4;
    } else if (i == 45) { // -
        base64 = 62;
    } else if (i == 95) { // _
        base64 = 63;
    }
    return base64;
}

/**
Takes as input a base64url character (in ASCII) and outputs
- a bit: 1 if the character is a valid base64url character, 0 otherwise
- a 6-bit value: the decoded base64 char

Cost: 73 constraints

- in:           The base64url character.
- isBase64:     A bit (0 or 1)
- base64Index:  The index of the base64url character in the base64url alphabet.

Notes:
1. If in is an invalid base64url character in the range [0, 256), then isBase64 = 0
    and we do not constrain base64Index.
2. For valid base64url characters, base64Index is constrained to be the correct value.
    E.g., if in = 66 ('B') then base64Index = 1 and isBase64 = 1
3. For characters outside the above range, the circuit might
    either throw a false assertion (in LessThan or GreaterThan) (or)
    set isBase64 = 0.
*/
template DecodeBase64URLChar() {
    signal input in;
    signal output isBase64;
    signal output base64Index;

    // Compute the base64 representation of in, e.g., if in = 66 ('B') then base64Index = 1
    //  This step does not add any constraints. 
    //  We check the correctness of the base64 representation next.
    base64Index <-- asciiToBase64UrlIndex(in);

    component lt91;
    lt91 = LessThan(8);
    lt91.in[0] <== in;
    lt91.in[1] <== 91;

    component gt64;
    gt64 = GreaterThan(8);
    gt64.in[0] <== in;
    gt64.in[1] <== 64;

    // If in is in [65, 90], then base64Index = in - 65 (line 8 of asciiToBase64Url)
    component forceequal1;
    forceequal1 = AssertEqualIfEnabled();
    forceequal1.enabled <== lt91.out * gt64.out;
    forceequal1.in[0] <== base64Index;
    forceequal1.in[1] <== in - 65;

    component lt123;
    lt123 = LessThan(8);
    lt123.in[0] <== in;
    lt123.in[1] <== 123;

    component gt96;
    gt96 = GreaterThan(8);
    gt96.in[0] <== in;
    gt96.in[1] <== 96;

    // If in is in [97, 122], then base64Index = in - 71 (line 10 of asciiToBase64Url)
    component forceequal2;
    forceequal2 = AssertEqualIfEnabled();
    forceequal2.enabled <== lt123.out * gt96.out;
    forceequal2.in[0] <== base64Index;
    forceequal2.in[1] <== in - 71;

    component lt58;
    lt58 = LessThan(8);
    lt58.in[0] <== in;
    lt58.in[1] <== 58;

    component gt47;
    gt47 = GreaterThan(8);
    gt47.in[0] <== in;
    gt47.in[1] <== 47;

    // If in is in [48, 57], then base64Index = in + 4 (line 12 of asciiToBase64Url)
    component forceequal3;
    forceequal3 = AssertEqualIfEnabled();
    forceequal3.enabled <== lt58.out * gt47.out;
    forceequal3.in[0] <== base64Index;
    forceequal3.in[1] <== in + 4;

    component eq45;
    eq45 = IsEqual();
    eq45.in[0] <== in;
    eq45.in[1] <== 45;

    // If in is 45, then base64Index = 62 (line 14 of asciiToBase64Url)
    component forceequal4;
    forceequal4 = AssertEqualIfEnabled();
    forceequal4.enabled <== eq45.out;
    forceequal4.in[0] <== base64Index;
    forceequal4.in[1] <== 62;

    component eq95;
    eq95 = IsEqual();
    eq95.in[0] <== in;
    eq95.in[1] <== 95;

    // If in is 95, then base64Index = 63 (line 16 of asciiToBase64Url)
    component forceequal5;
    forceequal5 = AssertEqualIfEnabled();
    forceequal5.enabled <== eq95.out;
    forceequal5.in[0] <== base64Index;
    forceequal5.in[1] <== 63;

    // Note: isBase64 = 0 happens only if all the enabled signals are 0. 
    //  This is because all the enabled signals are guaranteed to be either 0 or 1.
    isBase64 <== (forceequal1.enabled + forceequal2.enabled + forceequal3.enabled + forceequal4.enabled + forceequal5.enabled);
}

template StrictDecodeB64String(n) {
    signal input in[n];
    signal output out[n * 6];

    for (var i = 0; i < n; i++) {
        var (isBase64, base64Index) = DecodeBase64URLChar()(in[i]);
        isBase64 === 1;
        var bits[6] = Num2BitsBE(6)(base64Index);
        for (var j = 0; j < 6; j++) {
            out[i * 6 + j] <== bits[j];
        }
    }
}

/**
DecodeB64String: Strictly decodes in[0..length]. 
For the rest, the output is constrained to be 0.
**/
template DecodeB64String(n) {
    signal input in[n];
    signal input length;
    signal output out[n * 6];

    signal enabled[n] <== LTBitVector(n)(length);

    for (var i = 0; i < n; i++) {
        var (isBase64, base64Index) = DecodeBase64URLChar()(in[i]);
        AssertEqualIfEnabled()(enabled[i], [isBase64, 1]);
        var bits[6] = Num2BitsBE(6)(base64Index * enabled[i]);
        for (var j = 0; j < 6; j++) {
            out[i * 6 + j] <== bits[j];
        }
    }
}
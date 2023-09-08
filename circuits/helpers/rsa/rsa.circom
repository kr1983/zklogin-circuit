pragma circom 2.1.3;

include "./fp.circom";

// Computes base^65537 mod modulus
// Does not necessarily reduce fully mod modulus (the answer could be
// too big by a multiple of modulus)
template FpPow65537Mod(n, k) {
    signal input base[k];
    // Exponent is hardcoded at 65537
    signal input modulus[k];
    signal output out[k];

    component doublers[16];
    component adder = FpMul(n, k);
    for (var i = 0; i < 16; i++) {
        doublers[i] = FpMul(n, k);
    }

    for (var j = 0; j < k; j++) {
        adder.p[j] <== modulus[j];
        for (var i = 0; i < 16; i++) {
            doublers[i].p[j] <== modulus[j];
        }
    }

    // doublers[i].out = base^(2^(i+1)) mod modulus
    for (var j = 0; j < k; j++) {
        doublers[0].a[j] <== base[j];
        doublers[0].b[j] <== base[j];
    }
    for (var i = 0; i + 1 < 16; i++) {
        for (var j = 0; j < k; j++) {
            doublers[i + 1].a[j] <== doublers[i].out[j];
            doublers[i + 1].b[j] <== doublers[i].out[j];
        }
    }

    // out = doublers[15].out * base mod modulus
    for (var j = 0; j < k; j++) {
        adder.a[j] <== base[j];
        adder.b[j] <== doublers[15].out[j];
    }
    for (var j = 0; j < k; j++) {
        out[j] <== adder.out[j];
    }
}

/**
RSA signature verifier

Assumes:
    - public exponent is 65537 
    - hashing algorithm is SHA-2.
    - the modulus and base_message are well-formed and range-checked (or otherwise trustworthy).
    - all inputs are in little-endian order.

Note: It is not necessary to check that the modulus is well-formed 
in the circuit because this happens at another place: 
we reveal the modulus (as part of all inputs hash) 
and it gets matched against the JWK outside the circuit.

Similarly, for base_message, the hash is computed inside the circuit,
so we do not need to check that it is well-formed.

Spec: https://datatracker.ietf.org/doc/html/rfc8017#section-9.2
Go: https://go.dev/src/crypto/rsa/pkcs1v15.go
**/
template RSAVerify65537() {
    var n = 64; // Limb width
    var k = 32; // Number of 64-bit limbs

    signal input signature[k];
    signal input modulus[k];
    signal input base_message[4];

    // Check that the signature is in proper form and reduced mod modulus.
    component signatureRangeCheck[k];
    component bigLessThan = BigLessThan(n, k);
    for (var i = 0; i < k; i++) {
        signatureRangeCheck[i] = Num2Bits(n);
        signatureRangeCheck[i].in <== signature[i];
        bigLessThan.a[i] <== signature[i];
        bigLessThan.b[i] <== modulus[i];
    }
    bigLessThan.out === 1;

    component bigPow = FpPow65537Mod(n, k);
    for (var i = 0; i < k; i++) {
        bigPow.base[i] <== signature[i];
        bigPow.modulus[i] <== modulus[i];
    }

    // Note that there is no need to check that each limb of bigPow.out is in range, 
    //  because it is done in FpMul.
    component bigLessThan2 = BigLessThan(n, k);
    for (var i = 0; i < k; i++) {
        bigLessThan2.a[i] <== bigPow.out[i];
        bigLessThan2.b[i] <== modulus[i];
    }
    bigLessThan2.out === 1;

    // 1. Check hashed data
    // 64 * 4 = 256 bit. the first 4 numbers
    for (var i = 0; i < 4; i++) {
        base_message[i] === bigPow.out[i];
    }

    // 2. Check hash prefix and 1 byte 0x00
    // sha256/152 bit
    // 0x3031300d060960864801650304020105000420 (or)
    // 0b00110000001100010011000000001101000001100000100101100000100001100100100000000001011001010000001100000100000000100000000100000101000000000000010000100000
    bigPow.out[4] === 217300885422736416;
    bigPow.out[5] === 938447882527703397;
    // // remain 24 bit
    component num2bits_6 = Num2Bits(n);
    num2bits_6.in <== bigPow.out[6];
    var remainsBits[32] = [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 1, 0, 0, 1, 1, 0, 0, 0, 0];
    for (var i = 0; i < 32; i++) {
        num2bits_6.out[i] === remainsBits[31 - i];
    }

    // 3. Check PS and em[1] = 1. the same code like golang std lib rsa.VerifyPKCS1v15
    for (var i = 32; i < n; i++) {
        num2bits_6.out[i] === 1;
    }

    for (var i = 7; i < 31; i++) {
        // 0b1111111111111111111111111111111111111111111111111111111111111111
        bigPow.out[i] === 18446744073709551615;
    }
    // 0b1111111111111111111111111111111111111111111111111
    bigPow.out[31] === 562949953421311;
}

pragma circom 2.1.3;

include "../../node_modules/circomlib/circuits/poseidon.circom";

include "misc.circom";

// We only care about collision resistance in that it is hard to find
// two vectors v1 and v2 such that H(v1) = H(v2) and v1.length = v2.length. 
// This is because everything in the circuit is fixed length. 
// One can see that it is satisfied by the below function. 
template Hasher(nInputs) {
    signal input in[nInputs];
    signal output out;

    component pos1, pos2;
    // See https://github.com/iden3/circomlib/blob/master/circuits/poseidon.circom#L78. 
    // It implicitly forces t <= 17 or nInputs <= 16. 
    if (nInputs <= 16) {
        out <== Poseidon(nInputs)(in);
    } else if (nInputs <= 32) {
        pos1 = Poseidon(16);
        pos2 = Poseidon(nInputs - 16);

        for (var i = 0; i < 16; i++) {
            pos1.inputs[i] <== in[i];
        }
        for (var i = 16; i < nInputs; i++) {
            pos2.inputs[i - 16] <== in[i];
        }

        out <== Poseidon(2)([
            pos1.out,
            pos2.out
        ]);
    } else { // Yet to be implemented
        1 === 0;
    }
}

// Returns the number of output chunks (each of size outWidth) needed to represent inBits.
function getBaseConvertedOutputSize(inBits, outWidth) {
    var outCount = inBits \ outWidth;
    if (inBits % outWidth != 0) {
        outCount++;
    }
    return outCount;
}

/**
ConvertBase: Converts a number from base 2^inWidth to base 2^outWidth.

- inWidth: The bitwidth of each input number.
- inCount: The number of input numbers.
- outWidth: The bitwidth of each output number.
- outCount: The number of output numbers. (Should be inCount * inWidth / outWidth, rounded up.)

In essence, we pad the bits (in big-endian) at the start with sufficiently many zeroes
until the number of bits is a multiple of outWidth.
*/
template ConvertBase(inWidth, inCount, outWidth, outCount) {
    signal input in[inCount];
    signal output out[outCount];

    var inBits = inCount * inWidth;
    var myOutCount = getBaseConvertedOutputSize(inBits, outWidth);
    assert(myOutCount == outCount);

    component expander[inCount];
    for (var i = 0; i < inCount; i++) {
        expander[i] = Num2BitsBE(inWidth);
        expander[i].in <== in[i];
    }

    signal bitsBE[inBits];
    for (var i = 0; i < inBits; i++) {
        var mB = i % inWidth;
        var m = (i - mB) \ inWidth;

        bitsBE[i] <== expander[m].out[mB];
    }

    // We convert things to little endian as it makes it 
    //  easy to just append zeroes at the end.
    signal bitsLE[inBits];
    for (var i = 0; i < inBits; i++) {
        bitsLE[i] <== bitsBE[inBits - 1 - i];
    }

    component compressor[outCount];
    for (var i = 0; i < outCount - 1; i++) {
        compressor[i] = Bits2Num(outWidth);
    }
    var outExtra = inBits % outWidth;
    if (outExtra == 0) {
        compressor[outCount - 1] = Bits2Num(outWidth);
    } else {
        compressor[outCount - 1] = Bits2Num(outExtra);
    }

    for (var e = 0; e < inBits; e++) {
        var oB = e % outWidth;
        var o = (e - oB) \ outWidth;

        compressor[o].in[oB] <== bitsLE[e];
    }

    for (var i = 0; i < outCount; i++) {
        out[i] <== compressor[outCount - 1 - i].out;
    }
}

template HashToField(inWidth, inLen) {
    assert(inWidth <= 253); // log(p) - 1

    var packWidth = 248; // smallest multiple of 8 less than log(p)
    signal input in[inLen];

    var outCount = getBaseConvertedOutputSize(inLen * inWidth, packWidth);
    signal packed[outCount] <== ConvertBase(inWidth, inLen, packWidth, outCount)(in);
    signal output out <== Hasher(outCount)(packed);
}

// Note: The result of this function is the same as 
// directly calling HashToField(8, inLen)(in).
// This is a more efficient implementation as it avoids the Num2Bits.
template HashBytesToField(inLen) {
    signal input in[inLen];
    var inWidth = 8;

    var packWidth = 248; // smallest multiple of 8 less than log(p)
    var outCount = getBaseConvertedOutputSize(inLen * inWidth, packWidth);

    // convert to little endian
    signal inLE[inLen];
    for (var i = 0; i < inLen; i++) {
        inLE[i] <== in[inLen - 1 - i];
    }

    var numSegmentsPerWord = 31; // 248 / 8
    component compressor[outCount];
    for (var i = 0; i < outCount - 1; i++) {
        compressor[i] = Segments2NumLE(numSegmentsPerWord, inWidth);
    }
    var outExtra = inLen % numSegmentsPerWord;
    if (outExtra == 0) {
        compressor[outCount - 1] = Segments2NumLE(numSegmentsPerWord, inWidth);
    } else {
        compressor[outCount - 1] = Segments2NumLE(outExtra, inWidth);
    }

    for (var i = 0; i < inLen; i++) {
        var oB = i % numSegmentsPerWord;
        var o = (i - oB) \ numSegmentsPerWord;

        compressor[o].in[oB] <== inLE[i];
    }

    signal packed[outCount];
    for (var i = 0; i < outCount; i++) {
        packed[i] <== compressor[outCount - 1 - i].out;
    }

    signal output out <== Hasher(outCount)(packed);
}

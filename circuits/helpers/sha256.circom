pragma circom 2.1.3;

include "../../node_modules/circomlib/circuits/sha256/constants.circom";
include "../../node_modules/circomlib/circuits/sha256/sha256compression.circom";
include "../../node_modules/circomlib/circuits/comparators.circom";
include "misc.circom";
include "strings.circom";

/**
SHA256 variable length: Calculates the SHA256 hash of in[0:num_sha2_blocks-1]

Like Sha256 from circomlib, it assumes that the input is padded.

Construction Parameters:
    - nBlocks:      Maximum number of 512-bit blocks

Inputs:
    - in:           An array of blocks exactly nBlocks in length.
                    Each block is an array of 512 bits.
    - num_sha2_blocks:   Number of blocks to consider from the input.
    
Outputs:
    - out:      An array of 256 bits corresponding to the SHA256 output.
                We hash the blocks starting from in[0] upto in[num_sha2_blocks-1] (inclusive).

Assumes:
    - in is padded appropriately.
*/
template SHA256_varlen(nBlocks) {
    signal input in[nBlocks][512];
    signal input num_sha2_blocks;
    
    signal output out[256];

    component ha0 = H(0);
    component hb0 = H(1);
    component hc0 = H(2);
    component hd0 = H(3);
    component he0 = H(4);
    component hf0 = H(5);
    component hg0 = H(6);
    component hh0 = H(7);

    component sha256compression[nBlocks];

    for(var i = 0; i < nBlocks; i++) {
        sha256compression[i] = Sha256compression();
        if (i==0) {
            for(var k = 0; k < 32; k++) {
                sha256compression[i].hin[0*32+k] <== ha0.out[k];
                sha256compression[i].hin[1*32+k] <== hb0.out[k];
                sha256compression[i].hin[2*32+k] <== hc0.out[k];
                sha256compression[i].hin[3*32+k] <== hd0.out[k];
                sha256compression[i].hin[4*32+k] <== he0.out[k];
                sha256compression[i].hin[5*32+k] <== hf0.out[k];
                sha256compression[i].hin[6*32+k] <== hg0.out[k];
                sha256compression[i].hin[7*32+k] <== hh0.out[k];
            }
        } else {
            for(var k = 0; k < 32; k++) {
                sha256compression[i].hin[32*0+k] <== sha256compression[i-1].out[32*0+31-k];
                sha256compression[i].hin[32*1+k] <== sha256compression[i-1].out[32*1+31-k];
                sha256compression[i].hin[32*2+k] <== sha256compression[i-1].out[32*2+31-k];
                sha256compression[i].hin[32*3+k] <== sha256compression[i-1].out[32*3+31-k];
                sha256compression[i].hin[32*4+k] <== sha256compression[i-1].out[32*4+31-k];
                sha256compression[i].hin[32*5+k] <== sha256compression[i-1].out[32*5+31-k];
                sha256compression[i].hin[32*6+k] <== sha256compression[i-1].out[32*6+31-k];
                sha256compression[i].hin[32*7+k] <== sha256compression[i-1].out[32*7+31-k];
            }
        }

        for (var k = 0; k < 512; k++) {
            sha256compression[i].inp[k] <== in[i][k];
        }
    }
    
    signal eqs[nBlocks] <== OneBitVector(nBlocks)(num_sha2_blocks - 1);

    component totals[256];
    // For each bit of the output
    for(var k = 0; k < 256; k++) {
        totals[k] = Sum(nBlocks);

        // For each possible block
        for (var i = 0; i < nBlocks; i++) {
            // eqs[i].out is 1 if the index matches. As such, at most one input to totals is not 0.
            // The bit corresponding to the terminating data block will be raised
            totals[k].nums[i] <== eqs[i] * sha256compression[i].out[k];
        }
        out[k] <== totals[k].sum;
    }
}

/**
SHA2_Wrapper: Calculates the SHA2 hash of an arbitrarily shaped input using SHA256_varlen.
Additionally, it
    - Packs the output to the appropriate shape.
    - Checks that all inputs after num_sha2_blocks are indeed 0.

Construction Parameters:
    - inWidth:      Width of each input segment in bits
    - inCount:      Number of input segments
    - outWidth:     Width of each output segment in bits
    - outCount:     Number of output segments

Inputs:
    - in:       An array of inCount segments.
                Each segment is an array of inWidth bits.
    - num_sha2_blocks:   Number of blocks to consider from the input.

Outputs:
    - hash:     An array of outCount segments corresponding to the SHA256 output.
                Each segment is an array of outWidth bits.

Assumes:
    - in is padded appropriately.
*/
template Sha2_wrapper(inWidth, inCount, outWidth, outCount) {
    // Segments must divide evenly into 512 bit blocks
    var inBits = inCount * inWidth;
    assert(inBits % 512 == 0);

    signal input in[inCount];
    signal input num_sha2_blocks;

    assert(outWidth * outCount == 256);
    signal output hash[outCount];

    // The content is decomposed to 512-bit blocks for SHA-256
    var nBlocks = (inWidth * inCount) / 512;
    component sha256 = SHA256_varlen(nBlocks);

    // How many segments are in each block
    assert(inWidth <= 512);
    assert(512 % inWidth == 0);
    var nSegments = 512 / inWidth;
    component sha256_blocks[nBlocks][nSegments];

    // For each 512-bit block going into SHA-256
    for (var b = 0; b < nBlocks; b++) {
        // For each segment going into that block
        for (var s = 0; s < nSegments; s++) {
            // The index from the content is offset by the block we're composing times the number of segments per block,
            // s is then the segment offset within the block.
            var payloadIndex = (b * nSegments) + s;
            
            // Decompose each segment into an array of individual bits
            sha256_blocks[b][s] = Num2BitsBE(inWidth);
            sha256_blocks[b][s].in <== in[payloadIndex];
            
            // The bit index going into the current SHA-256 block is offset by the segment number times the bit width
            // of each content segment. sOffset + i is then the bit offset within the block (0-511).
            var sOffset = s * inWidth;
            for (var i = 0; i < inWidth; i++) {
                sha256.in[b][sOffset + i] <== sha256_blocks[b][s].out[i];
            }
        }
    }
    sha256.num_sha2_blocks <== num_sha2_blocks;

    /**
        Pack the output of the SHA-256 hash into a vector of size outCount where each element has outWidth bits.
    **/
    component hash_packer[outCount];
    for (var i = 0; i < outCount; i++) {
        hash_packer[i] = Bits2NumBE(outWidth);
        for (var j = 0; j < outWidth; j++) {
            hash_packer[i].in[j] <== sha256.out[i * outWidth + j];
        }
        hash_packer[i].out ==> hash[i];
    }

    /**
        Verify that content[i] for all blocks >= num_sha2_blocks is zero.
    **/
    signal gte[nBlocks] <== GTBitVector(nBlocks)(num_sha2_blocks - 1);

    for (var b = 0; b < nBlocks; b++) {
        for (var s = 0; s < nSegments; s++) {
            var payloadIndex = (b * nSegments) + s;
            gte[b] * in[payloadIndex] === 0;
        }
    }
}

/**
SHA2PadVerifier: Verifies that the padding of the SHA2 hash is correct.

<==header+payload==> <==sha2 padding==>
0101010101....101010 1 00...00 01010101
<--------L---------> 1 <--K--> <--64-->

Inputs:
    - M: The SHA2 padded message (plus zero padding)
    - length: The first "length" entries of M contain the SHA2 padded message.
    - length_without_padding: The message length before SHA2 padding.
                              Can alternatively be interpreted as the index at which the padding begins.
**/
template SHA2PadVerifier(inCount) {
    signal input M[inCount];
    signal input length;
    signal input length_without_padding; // in bytes

    var L_in_bytes = length_without_padding;
    var L = L_in_bytes * 8;
    var K = (length * 8) - L - 1 - 64;

    // Part of 4.1(b), namely, that K is the smallest, non-negative integer such that L + 1 + K + 64 is a multiple of 512
    RangeCheck(numBits(512), 511)(K); // 0 <= K < 512

    // 4.1(c): Check that the length is encoded correctly
    var last_8_bytes_index = length - 8;  // or (L + 1 + K) / 8
    signal encoded_length[8] <== SliceEfficient(inCount, 8)(
        M, last_8_bytes_index, 8
    );

    signal encoded_length_in_bits <== Segments2NumBE(8, 8)(encoded_length);
    encoded_length_in_bits === L;

    var rest_length_in_bytes = length - L_in_bytes - 8; // or (K + 1) / 8
    // max(rest_length_in_bytes) = (max(K) + 1) / 8 =  (1 + 511) / 8 = 64
    signal rest[64] <== SliceEfficient(inCount, 64)(
        M, L_in_bytes, rest_length_in_bytes
    );

    // 4.1(a): Check that the first bit is 1.
    // Note that L is a multiple of 8 (for JWTs), so in order to satisfy L + 1 + K = 448 (mod 512), it must be that K >= 7. 
    // Therefore, checking rest[0] == 128 works in this context.
    rest[0] === 128; // 10000000
    // 4.1(b): Check that the rest of the bits are 0.
    for (var i = 1; i < 64; i++) {
        rest[i] === 0;
    }
}
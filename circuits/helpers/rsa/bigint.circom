pragma circom 2.1.3;

include "../../../node_modules/circomlib/circuits/comparators.circom";
include "../../../node_modules/circomlib/circuits/bitify.circom";
include "../../../node_modules/circomlib/circuits/gates.circom";

include "bigint_func.circom";

/**
BigLessThan(n, k) checks if a < b (out = 1) or a >= b (out = 0)

The numbers a and b are represented as big integers in little-endian format.

n is the number of bits in each limb
k is the number of limbs
**/
template BigLessThan(n, k){
    signal input a[k];
    signal input b[k];
    signal output out;

    component lt[k];
    component eq[k];
    for (var i = 0; i < k; i++) {
        lt[i] = LessThan(n);
        lt[i].in[0] <== a[i];
        lt[i].in[1] <== b[i];
        eq[i] = IsEqual();
        eq[i].in[0] <== a[i];
        eq[i].in[1] <== b[i];
    }

    // ors[i] holds (lt[k - 1] || (eq[k - 1] && lt[k - 2]) .. || (eq[k - 1] && .. && eq[i + 1] && lt[i]))
    // eq_ands[i] holds (eq[k - 1] && .. && eq[i])
    // ands[i] holds (eq[k - 1] && .. && eq[i + 1] && lt[i])
    component ors[k - 1];
    component ands[k - 1];
    component eq_ands[k - 1];
    for (var i = k - 2; i >= 0; i--) {
        ands[i] = AND();
        eq_ands[i] = AND();
        ors[i] = OR();

        if (i == k - 2) {
           ands[i].a <== eq[k - 1].out;
           ands[i].b <== lt[k - 2].out;
           eq_ands[i].a <== eq[k - 1].out;
           eq_ands[i].b <== eq[k - 2].out;
           ors[i].a <== lt[k - 1].out;
           ors[i].b <== ands[i].out;
        } else {
           ands[i].a <== eq_ands[i + 1].out;
           ands[i].b <== lt[i].out;
           eq_ands[i].a <== eq_ands[i + 1].out;
           eq_ands[i].b <== eq[i].out;
           ors[i].a <== ors[i + 1].out;
           ors[i].b <== ands[i].out;
        }
     }
     out <== ors[0].out;
}

/**
CheckCarryToZero

Construction params:
    n: original number of bits in each limb
    m: actual number of bits in each limb (in[i] is in the range -2^(m-1) to 2^(m-1))
    k: number of limbs

Inputs:
    in: the limbs of the big integer

Implements the equality assertion described in Sec IV-B-4 of (https://ieeexplore.ieee.org/abstract/document/8418647).
In effect, this checks that the big integer is zero. In more detail, it checks that:
- in[0] % 2^n = 0, carry[0] = in[0] / 2^n
- (in[1] + carry[0]) % 2^n = 0, carry[1] = (in[1] + carry[0]) / 2^n
- ...
**/
template CheckCarryToZero(n, m, k) {
    assert(k >= 2);
    
    var EPSILON = 3;
    
    assert(m + EPSILON <= 253);

    signal input in[k];
    
    signal carry[k];
    component carryRangeChecks[k];
    for (var i = 0; i < k-1; i++) {
        carryRangeChecks[i] = Num2Bits(m + EPSILON - n); 
        if (i == 0) {
            carry[i] <-- in[i] / (1<<n);
            in[i] === carry[i] * (1<<n);
        }
        else {
            carry[i] <-- (in[i] + carry[i-1]) / (1<<n);
            in[i] + carry[i-1] === carry[i] * (1<<n);
        }
        // checking carry is in the range of - 2^(m-n-1+eps), 2^(m-n-1+eps)
        carryRangeChecks[i].in <== carry[i] + (1 << (m + EPSILON - n - 1));
    }
    in[k-1] + carry[k-2] === 0;
}

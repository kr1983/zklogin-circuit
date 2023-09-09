pragma circom 2.1.3;

include "../../../node_modules/circomlib/circuits/bitify.circom";

include "./bigint.circom";
include "./bigint_func.circom";

/**
FpMul: Multiplication in Fp.

Construction Params:
    n: bit width of each chunk
    k: number of chunk

Inputs: a, b (in chunked form). 
Note that a big integer is being stored as k chunks of n bits each.

Outputs: r (in chunked form) s.t. r mod p = (a * b) mod p where r < 2^(k * n)

Assumptions and limitations: 
1. The inputs must be less than p, i.e., a < p, b < p
2. The output r could be (a * b) mod p + xp for some x (provided r < 2^(k * n)).
   That is, we do not check if r < p to save on the comparison circuit.

Also note that many intermediate values "overflow" or "underflow"
    , i.e., contain chunks with > n bits.

The techniques are originally from xJsnark (https://ieeexplore.ieee.org/abstract/document/8418647)
 See Section IV-B-1 and IV-B-4.
**/
template FpMul(n, k) {
    assert(n + n + log_ceil(k) + 2 <= 252);
    signal input a[k];
    signal input b[k];
    signal input p[k];

    signal output out[k];

    // The product in evaluation domain
    signal v_ab[2*k-1];
    for (var x = 0; x < 2*k-1; x++) {
        var v_a = poly_eval(k, a, x);
        var v_b = poly_eval(k, b, x);
        v_ab[x] <== v_a * v_b;
    }

    // Moving to coefficient domain in order to calculate the actual product
    var ab[200] = poly_interp(2*k-1, v_ab);
    // ab_proper has length 2*k
    var ab_proper[200] = getProperRepresentation(n + n + log_ceil(k), n, 2*k-1, ab);

    var long_div_out[2][100] = long_div(n, k, k, ab_proper, p);

    // Since a < p and b < p, it must be that the quotient of the division (a * b) / p
    // is also less than p. So it should fit into k chunks.
    signal q[k];
    component q_range_check[k];
    signal r[k];
    component r_range_check[k];
    for (var i = 0; i < k; i++) {
        q[i] <-- long_div_out[0][i];
        q_range_check[i] = Num2Bits(n);
        q_range_check[i].in <== q[i];

        r[i] <-- long_div_out[1][i];
        r_range_check[i] = Num2Bits(n);
        r_range_check[i].in <== r[i];
    }

    // q and r are witnesses. Now we need to actually check that a*b - p*q - r = 0 (Ref Fig. 3 of xJsnark)
    signal v_pq_r[2*k-1];
    for (var x = 0; x < 2*k-1; x++) {
        var v_p = poly_eval(k, p, x);
        var v_q = poly_eval(k, q, x);
        var v_r = poly_eval(k, r, x);
        v_pq_r[x] <== v_p * v_q + v_r;
    }

    signal v_t[2*k-1];
    for (var x = 0; x < 2*k-1; x++) {
        v_t[x] <== v_ab[x] - v_pq_r[x];
    }

    var t[200] = poly_interp(2*k-1, v_t);
    component tCheck = CheckCarryToZero(n, n + n + log_ceil(k) + 2, 2*k-1);
    for (var i = 0; i < 2*k-1; i++) {
        tCheck.in[i] <== t[i];
    }

    for (var i = 0; i < k; i++) {
        out[i] <== r[i];
    }
}

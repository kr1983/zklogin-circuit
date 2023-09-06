# RSA Verification Circuits

Most of the code in this folder is from https://github.com/doubleblind-xyz/double-blind/tree/master/circuits. The main difference from their code is that we hardcode the PKCS15 padding verification. This part is taken from https://github.com/zkp-application/circom-rsa-verify (corresponds to lines 94-124 of rsa.circom).

Note that compared to doubleblind, we also add a check (lines 85-92 of rsa.circom) to make sure that bigPow.out is less than the modulus. (TODO: verify that this is indeed required for soundness.)

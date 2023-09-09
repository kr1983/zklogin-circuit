pragma circom 2.1.3;

include "zkLoginMain.circom";

component main {
    public [all_inputs_hash]
} = zkLogin(248, 64 * 25, 32, 115, 126, 145, 6, 165);
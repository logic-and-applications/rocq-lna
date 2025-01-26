
const general_tacs = ["Focus", "Unfocus", "SearchAbout", "Check", "Print", "Eval", "About", "Locate", "Proof", "Qed"];

// Placeholder for constructive proofs:
const allowed_tacs_lnaco = [
    "hyp", "assumption", "exact", "imp_e", "imp_i",
    "neg_e", "neg_i", "con_e1", "con_e2", "con_i",
    "dis_e", "dis_i1", "dis_i2", "iff_i", "iff_e1",
    "iff_e2", "all_e", "all_i", "exi_e", "exi_i",
    "equ_i", "equ_e", "equ_e'", "replace", "interval",
    "lin_solve", "apply", "unfold", "fold", "reflexivity",
    "symmetry", "box_e", "box_i", "Assumed", "AssumedAt",
    "replDiamond", "replBox", "T", "Four", "Five",
    "Truth", "Ki_e", "Ki_i", "C_e", "C_i",
    "KT", "K4", "K5", "CK", "C4",
    "C5", "EG_i", "EG_e", "CG_i", "CG_e",
    "KE", "EK_i", "CE", "CK",
].concat(general_tacs);

// Placeholder for classical proofs:
const allowed_tacs_lnacl = ["neg_e'"].concat(allowed_tacs_lnaco);

// Placeholder for classical proofs plus "LEM": (this is the default, it replaces the deprecated "benb_proof")
const allowed_tacs_lna = ["LEM"].concat(allowed_tacs_lnacl);

// Placeholder that in addition to the defaults allows the usage of "tauto":
const allowed_tacs_lnata = ["tauto"].concat(allowed_tacs_lna);

// Placeholder for (structural) induction. 
const allowed_tacs_lnain = [
    "absurd", "all", "assert", "auto", "case",
    "change", "Check", "clear", "compute", "constructor",
    "contradiction", "cut", "destruct", "discriminate", "easy",
    "elim", "elimtype", "exists", "field", "firstorder",
    "generalization", "induction", "intro", "intros", "intuition",
    "inversion", "inversion_clear", "left", "Print", "refine",
    "repeat", "rewrite", "right", "ring", "ring_simplify",
    "simpl", "spec", "split", "trivial", "try",
    "f_equal",
].concat(allowed_tacs_lnata);

// Placeholder that in addition to the defaults allows the usage of "pose proof":
const allowed_tacs_LnApose = ["pose proof"].concat(allowed_tacs_lna);

// ***************************************************************

type AllowList = { default: string[] } & Record<string, string[]>;
export const allowLists = {
    default: allowed_tacs_lna,

    lnaco_proof: allowed_tacs_lnaco,
    lnacl_proof: allowed_tacs_lnacl,
    lna_proof: allowed_tacs_lna,
    lnata_proof: allowed_tacs_lnata,
    lnain_proof: allowed_tacs_lnain,
    lnapose_proof: allowed_tacs_LnApose,
} as const satisfies AllowList;
export type pragma = keyof typeof allowLists;
export const pragmas = Object.keys(allowLists);

export default allowLists;


const general_tacs = ["Focus", "Unfocus", "SearchAbout", "Check", "Print", "Eval", "About", "Locate", "Proof", "Qed"];

// Placeholder voor constructieve bewijzen:
const allowed_tacs_benbco = [
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

// Placeholder voor klassieke bewijzen:
const allowed_tacs_benbcl = ["neg_e'"].concat(allowed_tacs_benbco);

// Placeholder voor klassieke bewijzen plus LEM: (de default, vervangt de vroegere "benb_proof")
const allowed_tacs_benb = ["LEM"].concat(allowed_tacs_benbcl);

// Placeholder die ook tauto toestaat:
const allowed_tacs_benbta = ["tauto"].concat(allowed_tacs_benb);

// Placeholder voor (structurele) inductie. EH: "Feitelijk zo'n beetje alle tactieken die ik ken zijn toegestaan."
const allowed_tacs_benbin = [
    "absurd", "all", "assert", "auto", "case",
    "change", "Check", "clear", "compute", "constructor",
    "contradiction", "cut", "destruct", "discriminate", "easy",
    "elim", "elimtype", "exists", "field", "firstorder",
    "generalization", "induction", "intro", "intros", "intuition",
    "inversion", "inversion_clear", "left", "Print", "refine",
    "repeat", "rewrite", "right", "ring", "ring_simplify",
    "simpl", "spec", "split", "trivial", "try",
    "f_equal",
].concat(allowed_tacs_benbta);

const allowed_tacs_LnApose = ["pose proof"].concat(allowed_tacs_benb);

// ***************************************************************

export const allowLists = {
    default: allowed_tacs_benb,

    benbco_proof: allowed_tacs_benbco,
    benbcl_proof: allowed_tacs_benbcl,
    benb_proof: allowed_tacs_benb,
    benbta_proof: allowed_tacs_benbta,
    benbin_proof: allowed_tacs_benbin,
    lnapose_proof: allowed_tacs_LnApose,
} as const;
export type pragma = keyof typeof allowLists;
export const pragmas = Object.keys(allowLists);

export default allowLists;
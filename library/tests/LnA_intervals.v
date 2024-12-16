Require Import LnA.LnA.
Require Import Strings.String.
Open Scope string_scope.

Parameter a b c:R.
Parameter x y z:Z.

Section test_interval_happy_R.
    Check "test_in_cc_happy".
    Lemma test_in_cc_happy: a in [b, c].
        interval.
        Show.
    Abort.
    Check "test_in_co_happy".
    Lemma test_in_co_happy: a in [b, c).
        interval.
        Show.
    Abort.
    Check "test_in_oc_happy".
    Lemma test_in_oc_happy: a in (b, c].
        interval.
        Show.
    Abort.
    Check "test_in_oo_happy".
    Lemma test_in_oo_happy: a in (b, c).
        interval.
        Show.
    Abort.
End test_interval_happy_R.

Open Scope Z_scope.
Section test_interval_happy_Z.
    Check "test_in_ccZ_happy".
    Lemma test_in_ccZ_happy: x in [y, z].
        interval.
        Show.
    Abort.
    Check "test_in_coZ_happy".
    Lemma test_in_coZ_happy: x in [y, z].
        interval.
        Show.
    Abort.
    Check "test_in_ocZ_happy".
    Lemma test_in_ocZ_happy: x in [y, z].
        interval.
        Show.
    Abort.
    Check "test_in_ooZ_happy".
    Lemma test_in_ooZ_happy: x in [y, z].
        interval.
        Show.
    Abort.
End test_interval_happy_Z.

Section test_interval_sad.
    Check "test_interval_sad".
    Lemma test_interval_sad: True.
        Fail interval.
    Abort.
End test_interval_sad.
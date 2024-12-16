Require Import LnA.LnA.
Require Import Strings.String.
Open Scope string_scope.

Parameter a b c: Prop.
Parameter X Y Z: Set.
Parameter x x1 x2 x3: X.
Parameter y: Y.
Parameter z: Z.

Section test_con_i.
    Check "happy_test_con_i".
    Lemma happy_test_con_i : a /\ b.
        con_i.
        Show.
    Abort.
End test_con_i.
Section test_con_e1.
    Check "happy_test_con_e1".
    Lemma happy_test_con_e1 : a.
        con_e1 b.
        Show.
    Abort.
End test_con_e1.
Section test_con_e2.
    Check "happy_test_con_e2".
    Lemma happy_test_con_e2 : b.
        con_e2 a.
        Show.
    Abort.
End test_con_e2.
Section test_dis_i1.
    Check "happy_test_dis_i1".
    Lemma happy_test_dis_i1 : a \/ b.
        dis_i1.
        Show.
    Abort.
End test_dis_i1.
Section test_dis_i2.
    Check "happy_test_dis_i2".
    Lemma happy_test_dis_i2 : a \/ b.
        dis_i2.
        Show.
    Abort.
End test_dis_i2.
Section test_dis_e.
    Check "happy_test_dis_e".
    Lemma happy_test_dis_e : a.
        dis_e (a \/ b) H1 H2.
        Show.
    Abort.
End test_dis_e.
Section test_imp_i.
    Check "happy_test_imp_i".
    Lemma happy_test_imp_i : a -> b.
        imp_i H.
        Show.
    Abort.
End test_imp_i.
Section test_imp_e.
    Check "happy_test_imp_e".
    Lemma happy_test_imp_e : b.
        imp_e a.
        Show.
    Abort.
End test_imp_e.
Section test_all_i.
    Check "happy_test_all_i".
    Lemma happy_test_all_i : forall xQuant:X, xQuant = xQuant.
        all_i xNew.
        Show.
    Abort.
End test_all_i.
Section test_all_e.
    Check "happy_test_all_e".
    Lemma happy_test_all_e : x = x.
        all_e (forall xQuant:X, xQuant=xQuant) x.
        Show.
    Abort.
End test_all_e.
Section test_eqv_i.
    Check "happy_test_eqv_i".
    Lemma happy_test_eqv_i : a <-> b.
        eqv_i.
        Show.
    Abort.
End test_eqv_i.
Section test_eqv_e1.
    Check "happy_test_eqv_e1".
    Lemma happy_test_eqv_e1 : b -> a.
        eqv_e1.
        Show.
    Abort.
End test_eqv_e1.
Section test_eqv_e2.
    Check "happy_test_eqv_e2".
    Lemma happy_test_eqv_e2 : a -> b.
        eqv_e2.
        Show.
    Abort.
End test_eqv_e2.
Section test_iff_i.
    Check "happy_test_iff_i".
    Lemma happy_test_iff_i : a <-> b.
        iff_i H1 H2.
        Show.
    Abort.
End test_iff_i.
Section test_iff_e1.
    Check "happy_test_iff_e1".
    Lemma happy_test_iff_e1 : a.
        iff_e1 b.
        Show.
    Abort.
End test_iff_e1.
Section test_iff_e2.
    Check "happy_test_iff_e2".
    Lemma happy_test_iff_e2 : b.
        iff_e2 a.
        Show.
    Abort.
End test_iff_e2.
Section test_neg_e.
    Check "happy_test_neg_e".
    Lemma happy_test_neg_e : c.
        neg_e a.
        Show.
    Abort.
End test_neg_e.
Section test_fls_e.
    Check "happy_test_fls_e".
    Lemma happy_test_fls_e : True.
        fls_e.
        Show.
    Abort.
End test_fls_e.
Section test_LEM.
    Check "happy_test_LEM".
    Lemma happy_test_LEM : a \/ ~a.
        LEM.
        Show.
    Abort.
End test_LEM.
Section test_exi_i.
    Check "happy_test_exi_i".
    Lemma happy_test_exi_i : exists xQuant:X, xQuant=xQuant.
        exi_i x1.
        Show.
    Abort.
End test_exi_i.
Section test_exi_e.
    Check "happy_test_exi_e".
    Lemma happy_test_exi_e : x1=x1.
        exi_e (exists xQuant:X, xQuant=xQuant) xNew H.
        Show.
    Abort.
End test_exi_e.
Section test_hyp.
    Check "happy_test_hyp".
    Lemma happy_test_hyp (H: a) : a.
        hyp H.
        Show.
    Abort.
End test_hyp.
Section test_neg_i.
    Check "happy_test_neg_i".
    Lemma happy_test_neg_i : ~a.
        neg_i b H.
        Show.
    Abort.
End test_neg_i.
Section test_neg_e'.
    Check "happy_test_neg_e".
    Lemma happy_test_neg_e' : True.
        neg_e' a H.
        Show.
    Abort.
End test_neg_e'.
Section test_replace.
    Check "happy_test_replace".
    Lemma happy_test_replace : a.
        replace a with b.
        Show.
    Abort.
End test_replace.
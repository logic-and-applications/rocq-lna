Require Import LnA.LnA.
Require Import Strings.String.
Open Scope string_scope.

Parameter x y z:R.
Parameter foo: R -> Prop.

Section test_lin_solve_clear_tactic_happy.
    Check "test_lin_solve_clear_tactic_happy".
    Lemma test_lin_solve_clear_tactic_happy
        (H0: foo x)
        (H1: x > 0 /\ x < 10)
        (H2: x > 0)
        (H3: x < 10)
        : x < 100.
        lin_solve_clear_tactic.
        Show.
        Abort.
End test_lin_solve_clear_tactic_happy.

Section test_lin_solve.
    Check "test_lin_solve_happy".
    Lemma test_lin_solve_happy
        (H0: foo x)
        (H1: x > 0 /\ x < 10)
        (H2: x > 0)
        (H3: x < 10)
        : x < 100.
        lin_solve.
    Qed.
    Check "test_lin_solve_sad_wrong_goal".
    Lemma test_lin_solve_sad_wrong_goal
        (H0: foo x)
        (H1: x > 0 /\ x < 10)
        (H2: x > 0)
        (H3: x < 10)
        : True.
        Fail lin_solve.
    Abort.
    Check "test_lin_solve_sad_cannot_solve".
    Lemma test_lin_solve_sad_cannot_solve
        (H0: foo x)
        (H1: x > 0 /\ x < 10)
        (H2: x > 0)
        (H3: x < 10)
        : x > 100.
        Fail lin_solve.
    Abort.
    Check "test_lin_solve_sad_no_prep".
    Lemma test_lin_solve_sad_no_prep
        (H0: foo x)
        (H1: x > 0 /\ x < 10)
        : x < 100.
        Fail lin_solve.
    Abort.
End test_lin_solve.

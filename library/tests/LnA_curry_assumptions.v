Require Import LnA.LnA.
Require Import Strings.String.
Open Scope string_scope.

Parameter a a1 a2 a3 a4 a5 a6 a7 a8 a9 a10: Prop.

Section test_curry_assumptions_happy.
    Check "test_curry_assumptions_happy_2".
    Lemma test_curry_assumptions_happy_2:
        (a1 /\ a2) -> a.
        curry_assumptions. 
        Show.
    Abort.
    Check "test_curry_assumptions_happy_3".
    Lemma test_curry_assumptions_happy_3:
        (a1 /\ a2 /\ a3) -> a.
        curry_assumptions. 
        Show.
    Abort.
    Check "test_curry_assumptions_happy_4".
    Lemma test_curry_assumptions_happy_4:
        (a1 /\ a2 /\ a3 /\ a4) -> a.
        curry_assumptions. 
        Show.
    Abort.
    Check "test_curry_assumptions_happy_5".
    Lemma test_curry_assumptions_happy_5:
        (a1 /\ a2 /\ a3 /\ a4 /\ a5) -> a.
        curry_assumptions. 
        Show.
    Abort.
    Check "test_curry_assumptions_happy_6".
    Lemma test_curry_assumptions_happy_6:
        (a1 /\ a2 /\ a3 /\ a4 /\ a5 /\ a6) -> a.
        curry_assumptions. 
        Show.
    Abort.
    Check "test_curry_assumptions_happy_7".
    Lemma test_curry_assumptions_happy_7:
        (a1 /\ a2 /\ a3 /\ a4 /\ a5 /\ a6 /\ a7) -> a.
        curry_assumptions. 
        Show.
    Abort.
    Check "test_curry_assumptions_happy_8".
    Lemma test_curry_assumptions_happy_8:
        (a1 /\ a2 /\ a3 /\ a4 /\ a5 /\ a6 /\ a7 /\ a8) -> a.
        curry_assumptions. 
        Show.
    Abort.
    Check "test_curry_assumptions_happy_9".
    Lemma test_curry_assumptions_happy_9:
        (a1 /\ a2 /\ a3 /\ a4 /\ a5 /\ a6 /\ a7 /\ a8 /\ a9) -> a.
        curry_assumptions. 
        Show.
    Abort.
    Check "test_curry_assumptions_happy_10".
    Lemma test_curry_assumptions_happy_10:
        (a1 /\ a2 /\ a3 /\ a4 /\ a5 /\ a6 /\ a7 /\ a8 /\ a9 /\ a10) -> a.
        curry_assumptions. 
        Show.
    Abort.
    Check "test_curry_assumptions_happy_more".
    Lemma test_curry_assumptions_happy_more:
        (a1 /\ a2 /\ a3 /\ a4 /\ a5 /\ a6 /\ a7 /\ a8 /\ a9 /\ a10 /\ a /\ a /\ a /\ a) -> a.
        curry_assumptions. 
        Show.
    Abort.
End test_curry_assumptions_happy.

Section test_curry_assumptions_sad.
    Check "test_curry_assumptions_sad".
    Lemma test_curry_assumptions_sad: True.
        Fail curry_assumptions.
    Abort.
End test_curry_assumptions_sad.
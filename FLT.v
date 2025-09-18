From Coq Require Import Arith Lia ZArith Ring.

Open Scope Z_scope.

(* Algebraic consequences of introducing parameters m and p. *)
Lemma sum_diff_from_parameters
      (n : nat) (m p : Z) :
  let z := m ^ Z.of_nat n + p ^ Z.of_nat n in
  let x := m ^ Z.of_nat n - p ^ Z.of_nat n in
  z + x = 2 * m ^ Z.of_nat n /\
  z - x = 2 * p ^ Z.of_nat n.
Proof.
  intros z x; unfold z, x; split; nia.
Qed.

Corollary parity_condition
          (n : nat) (m p : Z) :
  let z := m ^ Z.of_nat n + p ^ Z.of_nat n in
  let x := m ^ Z.of_nat n - p ^ Z.of_nat n in
  Z.even (z + x) = true /\
  Z.even (z - x) = true.
Proof.
  intros z x.
  destruct (sum_diff_from_parameters n m p) as [Hzx Hzx'].
  split.
  - replace (z + x) with (2 * m ^ Z.of_nat n) by exact Hzx.
    rewrite Z.even_mul; simpl; reflexivity.
  - replace (z - x) with (2 * p ^ Z.of_nat n) by exact Hzx'.
    rewrite Z.even_mul; simpl; reflexivity.
Qed.

(* A concrete obstruction: picking values with odd z + x prevents the
   existence of integers m and p as in the text. *)
Example no_parameters_for_example :
  ~ (exists m p : Z,
        2%Z = m ^ Z.of_nat 3 + p ^ Z.of_nat 3 /\
        1%Z = m ^ Z.of_nat 3 - p ^ Z.of_nat 3).
Proof.
  intros [m [p [Hz Hx]]].
  destruct (sum_diff_from_parameters 3 m p) as [Hsum _].
  rewrite <- Hz, <- Hx in Hsum.
  replace (2 + 1)%Z with 3%Z in Hsum by lia.
  assert (Hodd : Z.even 3 = false) by reflexivity.
  assert (Heven : Z.even 3 = true).
  { rewrite Hsum.
    rewrite Z.even_mul; simpl; reflexivity. }
  now rewrite Hodd in Heven.
Qed.

Close Scope Z_scope.
Open Scope nat_scope.

(* Exponential growth compared to linear growth for powers of 2. *)
Lemma pow2_gt_linear_shift (k : nat) :
  2 ^ (k + 3) > 2 * (k + 3).
Proof.
  induction k as [|k IH]; simpl.
  - lia.
  - replace (S k + 3) with (k + 4) by lia.
    replace (2 ^ (S k + 3)) with (2 * 2 ^ (k + 3)) by
        (replace (S k + 3) with (S (k + 3)) by lia;
         rewrite Nat.pow_succ_r; lia).
    assert (Htmp : 2 * 2 ^ (k + 3) > 4 * (k + 3)) by nia.
    apply Nat.le_lt_trans with (m := 4 * (k + 3)).
    + lia.
    + exact Htmp.
Qed.

Lemma pow2_gt_linear (n : nat) :
  3 <= n -> 2 ^ n > 2 * n.
Proof.
  intros Hn.
  destruct (Nat.le_exists_sub 3 n Hn) as [k [Hk _]].
  rewrite Hk.
  replace (3 + k) with (k + 3) by lia.
  apply pow2_gt_linear_shift.
Qed.

Lemma pow_eq_linear_cases (n : nat) :
  2 ^ n = 2 * n -> n = 0 \/ n = 1 \/ n = 2.
Proof.
  destruct n as [|n].
  - simpl. intro H. now left.
  - destruct n as [|n].
    + simpl. intro H. right; left; lia.
    + destruct n as [|n].
      * simpl. intro H. right; right; lia.
      * intro H.
        assert (3 <= S (S (S n))) by lia.
        specialize (pow2_gt_linear _ H0) as Hgt.
        rewrite H in Hgt. lia.
Qed.

Lemma pow_eq_linear_positive (n : nat) :
  2 ^ n = 2 * n -> n = 1 \/ n = 2.
Proof.
  intro H.
  destruct (pow_eq_linear_cases n H) as [H0 | [H1 | H2]].
  - subst n. discriminate.
  - now left.
  - now right.
Qed.

(* Exponential growth compared to linear growth for powers of 3. *)
Lemma pow3_gt_linear_shift (k : nat) :
  3 ^ (k + 1) > 2 * (k + 1).
Proof.
  induction k as [|k IH]; simpl.
  - lia.
  - replace (S k + 1) with (k + 2) by lia.
    replace (3 ^ (S k + 1)) with (3 * 3 ^ (k + 1)) by
        (replace (S k + 1) with (S (k + 1)) by lia;
         rewrite Nat.pow_succ_r; lia).
    assert (Htmp : 3 * 3 ^ (k + 1) > 3 * (2 * (k + 1))) by nia.
    apply Nat.le_lt_trans with (m := 3 * (2 * (k + 1))).
    + lia.
    + exact Htmp.
Qed.

Lemma pow3_gt_linear (n : nat) :
  1 <= n -> 3 ^ n > 2 * n.
Proof.
  intros Hn.
  destruct (Nat.le_exists_sub 1 n Hn) as [k [Hk _]].
  rewrite Hk.
  replace (1 + k) with (k + 1) by lia.
  apply pow3_gt_linear_shift.
Qed.

(* The equation o^n = 2n with integer o > 1 forces o = 2 and n in {1,2}. *)
Lemma integer_solution_o (o n : nat) :
  1 < o -> 1 <= n -> o ^ n = 2 * n -> o = 2 /\ (n = 1 \/ n = 2).
Proof.
  intros Ho Hn HoEq.
  destruct o as [|o]; [lia|].
  destruct o as [|o]; [lia|].
  destruct o as [|o].
  - (* o = 2 *)
    simpl in HoEq.
    split; [reflexivity|].
    apply pow_eq_linear_positive in HoEq.
    assumption.
  - (* o >= 3 leads to contradiction *)
    assert (Hcomp : 3 ^ n <= (S (S (S o))) ^ n).
    { apply Nat.pow_le_mono_l; lia. }
    specialize (pow3_gt_linear n Hn) as Hgt.
    rewrite HoEq in Hcomp.
    lia.
Qed.

Section DocumentLogic.

Hypothesis document_step :
  forall (n x y z : nat),
    2 < n ->
    x ^ n + y ^ n = z ^ n ->
    exists o : nat, 1 < o /\ o ^ n = 2 * n.

Theorem fermat_last_theorem_document :
  forall (n x y z : nat),
    2 < n ->
    x ^ n + y ^ n = z ^ n -> False.
Proof.
  intros n x y z Hn Heq.
  destruct (document_step n x y z Hn Heq) as [o [Ho_gt HoEq]].
  destruct (integer_solution_o o n) as [Ho2 Hcases].
  - exact Ho_gt.
  - lia.
  - exact HoEq.
  - destruct Hcases as [Hn1 | Hn2]; lia.
Qed.

End DocumentLogic.

(* Under the document's assumption, the Fermat equation has no solutions
   in natural numbers for exponents above 2. *)



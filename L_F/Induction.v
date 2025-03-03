From LF Require Export Basics.

Theorem add_0_r_firsttry : forall n:nat,
  n + 0 = n.
Proof.
intros n.
induction n as [| n' IHn].
reflexivity.
simpl.
rewrite -> IHn.
reflexivity.
Qed.

Theorem minus_n_n : forall n, minus n n = 0.
Proof.
intro n.
induction n as [| n' IHn].
reflexivity.
simpl.
rewrite -> IHn.
reflexivity.
Qed.

Theorem mul_0_r: forall n:nat, n*0=0.
Proof.
intro n.
induction n as [| n' IHn].
reflexivity.
simpl.
rewrite -> IHn.
reflexivity.
Qed.

Theorem plus_n_Sm : forall n m : nat,
  S (n + m) = n + (S m).
Proof.
intros.
induction n as [|n'].
simpl.
reflexivity.
simpl.
rewrite -> IHn'.
reflexivity.
Qed.

Theorem add_comm : forall n m : nat,
  n + m = m + n.
Proof.
intros.
induction n.
simpl.
rewrite add_0_r_firsttry.
reflexivity.
simpl.
rewrite -> IHn.
rewrite plus_n_Sm.
reflexivity.
Qed.

Theorem add_assoc: forall n m p : nat, n+(m+p) = (n+m)+p.
Proof.
intros.
induction n.
simpl.
reflexivity.
simpl.
rewrite <- IHn.
reflexivity.
Qed.

Fixpoint double (n:nat) :=
  match n with
  | O => O
  | S n' => S (S (double n'))
  end.

Lemma double_plus : forall n, double n = n+n.
Proof.
intros.
induction n.
simpl.
reflexivity.
simpl.
rewrite -> IHn.
rewrite -> plus_n_Sm.
reflexivity.
Qed.

Theorem eqb_refl : forall n : nat,
  (n =? n) = true.
Proof.
intros.
induction n.
reflexivity.
simpl.
rewrite <- IHn.
reflexivity.
Qed.

Fixpoint even (n:nat): bool:=
match n with
| O => true
| S O => false
| S ( S n') => even(n')
end.

Theorem even_S': forall n:nat, even (S n) = negb(even n).
Proof.
intros.
induction n.
reflexivity.
assert (forall x y: bool, y = negb x -> x = negb y).
intro x.
intro y.
destruct x.
simpl.
intro.
rewrite -> H.
reflexivity.
simpl.
intro.
rewrite -> H.
reflexivity.
specialize (H (even (n))).
specialize (H ((even (S n)))).
apply H in IHn.
rewrite <- IHn.
simpl.
reflexivity.
Qed.


Theorem even_S: forall n:nat, even (S n) = negb(even n).
Proof.
intros.
induction n.
reflexivity.
rewrite -> IHn.
simpl.
rewrite double_negation.
reflexivity.
Qed.

(*rewrite tactic searches from outside, matches outermost*)


Theorem add_shuffle3 : forall n m p : nat,
  n + (m + p) = m + (n + p).
Proof.
intros.
assert (H: n+(m+p) = (n+m)+p).
{ rewrite add_assoc. reflexivity. }
rewrite -> H.
assert (H2: n+m = m+n). 
{
	rewrite add_comm. reflexivity.
}
rewrite -> H2.
assert (H3: m+(n+p) = (m+n)+p).
{
	rewrite add_assoc. reflexivity.
}
rewrite H3.
reflexivity.
Qed.

Theorem helper : forall n k , n * S k = n + n*k.
Proof.
intros.
induction n.
reflexivity.
simpl.
rewrite IHn.
rewrite add_shuffle3.
reflexivity.
Qed.
(*
induction k.
assert (H1 : forall t , t*0 = 0).
intro.
induction t.
reflexivity.
simpl.
rewrite IHt.
reflexivity.
assert (H2: forall t, t*1=t).
intro.
induction t.
reflexivity.
simpl.
rewrite IHt.
reflexivity.
specialize (H1 n) as H1n.
specialize (H2 n) as H2n.
rewrite H1n.
rewrite H2n.
rewrite add_0_r_firsttry.
reflexivity.
*)


Theorem mul_comm : forall m n : nat,
  m * n = n * m.
Proof.
induction n.
simpl.
induction m.
reflexivity.
simpl.
rewrite IHm.
reflexivity.
simpl.
rewrite <- IHn.
rewrite helper.
reflexivity.
Qed.

Check leb.
Theorem plus_leb_compat_l : forall n m p : nat,
  n <=? m = true -> (p + n) <=? (p + m) = true.
Proof.
intros.
induction p.
simpl.
rewrite H.
reflexivity.
simpl.
rewrite IHp.
reflexivity.
Qed.

Theorem leb_refl : forall n:nat,
  (n <=? n) = true.
Proof.
intros.
induction n.
reflexivity.
simpl.
rewrite IHn.
reflexivity.
Qed.

Theorem zero_neqb_S : forall n:nat,
  0 =? (S n) = false.
Proof.
intros.
simpl.
reflexivity.
Qed.

Theorem andb_false_r : forall b : bool,
  andb b false = false.
Proof.
intros.
destruct b.
reflexivity.
reflexivity.
Qed.

Theorem S_neqb_0 : forall n:nat,
  (S n) =? 0 = false.
Proof.
intros.
simpl.
reflexivity.
Qed.

Theorem mult_1_l : forall n:nat, 1 * n = n.
Proof.
intros.
induction n.
reflexivity.
rewrite <- IHn.
simpl.
rewrite add_0_r_firsttry.
reflexivity.
Qed.

Theorem all3_spec : forall b c : bool,
  orb
    (andb b c)
    (orb (negb b)
         (negb c))
  = true.
Proof.
intros.
destruct b.
simpl.
destruct c.
reflexivity.
reflexivity.
simpl.
reflexivity.
Qed.

Theorem mult_plus_distr_r : forall n m p : nat,
  (n + m) * p = (n * p) + (m * p).
Proof.
intros.
induction n.
simpl.
reflexivity.
simpl.
rewrite IHn.
rewrite add_assoc.
reflexivity.
Qed.

Theorem mult_assoc : forall n m p : nat,
  n * (m * p) = (n * m) * p.
Proof.
intros.
induction n.
simpl.
reflexivity.
simpl.
rewrite mult_plus_distr_r.
rewrite IHn.
reflexivity.
Qed.

Theorem add_shuffle3' : forall n m p : nat,
  n + (m + p) = m + (n + p).
Proof.
intros.
replace (n+(m+p)) with ((n+m)+p).
replace (m+(n+p)) with ((m+n)+p).
replace (n+m) with (m+n).
reflexivity.
rewrite add_comm.
reflexivity.
rewrite add_assoc.
reflexivity.
rewrite add_assoc.
reflexivity.
Qed.

Inductive bin : Type :=
  | Z
  | B0 (n : bin)
  | B1 (n : bin).

Fixpoint bin_to_nat(m: bin) : nat :=
match m with
| Z => 0
| B0 t => 2*bin_to_nat(t)
| B1 t => (2*bin_to_nat(t))+1
end.

Fixpoint incr(m: bin) : bin :=
match m with
| Z => B1 Z
| B0 t => B1 t
| B1 t => B0 (incr (t))
end.

Compute incr(B1 (B1 Z)).

Theorem bin_to_nat_pres_incr : forall b : bin,
  bin_to_nat (incr b) = 1 + bin_to_nat b.
Proof.
assert (H: forall t, t+1 = S t).
{
	intro.
	induction t.
	reflexivity.
	simpl.
	rewrite IHt.
	reflexivity.
}
intro b.
induction b.
reflexivity.
simpl.
rewrite add_0_r_firsttry.
specialize (H (bin_to_nat b + bin_to_nat b)) as Hb.
rewrite Hb.
reflexivity.
simpl.
rewrite IHb.
simpl.
rewrite add_0_r_firsttry.
specialize (H (bin_to_nat b)) as Hb.
rewrite <- Hb.
rewrite add_assoc.
reflexivity.
Qed.

Fixpoint nat_to_bin (n:nat) : bin :=
match n with
| 0 => Z
| S x => incr(nat_to_bin x)
end.

Theorem nat_bin_nat : forall n, bin_to_nat (nat_to_bin n) = n.
Proof.
intro n.
induction n.
reflexivity.
simpl.
rewrite bin_to_nat_pres_incr.
simpl.
rewrite IHn.
reflexivity.
Qed.

Compute nat_to_bin 016.

Lemma double_incr : forall n : nat, double (S n) = S (S (double n)).
Proof.
intros.
induction n.
reflexivity.
rewrite IHn.
simpl.
reflexivity.
Qed.

Definition double_bin (b:bin) : bin :=
match b with
| Z => Z
| b' => B0 b'
end.

Lemma double_incr_bin : forall b,
    double_bin (incr b) = incr (incr (double_bin b)).
Proof.
intros.
induction b.
reflexivity.
simpl.
reflexivity.
simpl.
reflexivity.
Qed.

Fixpoint normalize (b:bin) : bin :=
match b with
| Z => Z
| B0 x => double_bin (normalize x)
| B1 x => incr (double_bin (normalize x))
end.

Compute (normalize (B0 (B1 Z))).



Check double_incr_bin.
Check double_incr.
Check bin_to_nat_pres_incr.
Check double_plus.

Lemma btnpi: forall b:bin, bin_to_nat(incr b) = S (bin_to_nat b).
Proof.
intro.
assert (forall n, S n = 1 + n).
{
  simpl.
  reflexivity.
}
rewrite H.
apply bin_to_nat_pres_incr.
Qed.


Lemma zcase: forall b: bin, bin_to_nat(B0 b) = double (bin_to_nat b).
Proof.
intro.
simpl.
rewrite add_0_r_firsttry.
rewrite double_plus.
reflexivity.
Qed.

Lemma zcase2: forall n:nat, nat_to_bin(double n) = double_bin (nat_to_bin n).
Proof.
intro.
induction n.
reflexivity.
rewrite double_incr.
simpl.
rewrite double_incr_bin.
rewrite IHn.
reflexivity.
Qed.

Lemma ocase: forall b: bin, bin_to_nat(B1 b) = double(bin_to_nat b)+1.
Proof.
intro.
simpl.
rewrite add_0_r_firsttry.
rewrite double_plus.
reflexivity.
Qed.

Theorem bin_nat_bin : forall b, nat_to_bin (bin_to_nat b) = normalize b.
Proof.
intros.
induction b.
reflexivity.
{
  rewrite -> zcase.
  simpl.
  rewrite -> zcase2.
  rewrite IHb.
  reflexivity.
}
{
  rewrite -> ocase.
  assert (forall n, S n = n + 1).
  {
  intro.
  induction n.
  reflexivity.
  simpl.
  rewrite <- IHn.
  reflexivity.
  }
  rewrite <- H.
  rewrite <- zcase.
  simpl.
  rewrite add_0_r_firsttry.
  rewrite <- double_plus.
  rewrite zcase2.
  rewrite IHb.
  reflexivity.
}
Qed.


(*
simpl.
rewrite <- IHb.
rewrite -> add_0_r_firsttry.
rewrite <- double_semantics.
*)



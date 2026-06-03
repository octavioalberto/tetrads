import Mathlib

open Nat

namespace Tetrads

/-- The finite set appearing in the manuscript:
    `{1 ≤ n ≤ p - 1 : n! ≡ 1 mod p}`. -/
def factorialOneResidues (p : ℕ) : Finset ℕ :=
  (Finset.Icc 1 (p - 1)).filter fun n =>
    n.factorial ≡ 1 [MOD p]

/-- Wilson symmetry, in the form used in the manuscript.

If `p` is prime, `n` is odd, `0 ≤ n ≤ p - 1`, and `n! ≡ 1 mod p`,
then `(p - 1 - n)! ≡ 1 mod p`. -/
lemma cast_tail_zmod
    {p n : ℕ}
    (hn : n + 1 ≤ p) :
    ((p - 1 - n : ℕ) : ZMod p) = -((n + 1 : ℕ) : ZMod p) := by
  have hsum : p - 1 - n + (n + 1) = p := by
    omega
  have hzero :
      ((p - 1 - n : ℕ) : ZMod p) + ((n + 1 : ℕ) : ZMod p) = 0 := by
    rw [← Nat.cast_add, hsum]
    simp
  exact eq_neg_of_add_eq_zero_left hzero

lemma descFactorial_tail_zmod
    {p n : ℕ}
    (hn : n ≤ p - 1) :
    (((p - 1).descFactorial n : ℕ) : ZMod p)
      =
    (-1 : ZMod p)^n * ((n.factorial : ℕ) : ZMod p) := by
  induction n with
  | zero =>
      simp
  | succ n ih =>
      have hn' : n ≤ p - 1 := by omega
      have hn_tail : n + 1 ≤ p := by omega
      calc
        (((p - 1).descFactorial (n + 1) : ℕ) : ZMod p)
            =
          ((p - 1 - n : ℕ) : ZMod p)
            * (((p - 1).descFactorial n : ℕ) : ZMod p) := by
              simp [Nat.descFactorial_succ]
        _ =
          (-((n + 1 : ℕ) : ZMod p))
            * (((p - 1).descFactorial n : ℕ) : ZMod p) := by
              rw [cast_tail_zmod hn_tail]
        _ =
          (-((n + 1 : ℕ) : ZMod p))
            * ((-1 : ZMod p)^n * ((n.factorial : ℕ) : ZMod p)) := by
              rw [ih hn']
        _ =
          (-1 : ZMod p)^(n + 1)
            * (((n + 1).factorial : ℕ) : ZMod p) := by
              simp [Nat.factorial_succ]
              ring

lemma wilson_symmetry
    {p n : ℕ}
    (hp : Nat.Prime p)
    (hn_le : n ≤ p - 1)
    (hn_odd : Odd n)
    (hn_fac : ((n.factorial : ℕ) : ZMod p) = 1) :
    (((p - 1 - n).factorial : ℕ) : ZMod p) = 1 := by
  haveI : Fact (Nat.Prime p) := ⟨hp⟩

  have hsplit_nat :
      (p - 1 - n).factorial * (p - 1).descFactorial n
        =
      (p - 1).factorial :=
    Nat.factorial_mul_descFactorial hn_le

  have hsplit_zmod :
      (((p - 1 - n).factorial : ℕ) : ZMod p)
        * (((p - 1).descFactorial n : ℕ) : ZMod p)
        =
      -1 := by
    rw [← Nat.cast_mul, hsplit_nat]
    exact ZMod.wilsons_lemma p

  have hpow : (-1 : ZMod p)^n = -1 := by
   exact Odd.neg_one_pow hn_odd

  have htail :
      (((p - 1).descFactorial n : ℕ) : ZMod p) = -1 := by
    rw [descFactorial_tail_zmod hn_le, hpow, hn_fac]
    ring

  have h :
      (((p - 1 - n).factorial : ℕ) : ZMod p) * (-1) = -1 := by
    simpa [htail] using hsplit_zmod

  calc
    (((p - 1 - n).factorial : ℕ) : ZMod p)
        =
      -((((p - 1 - n).factorial : ℕ) : ZMod p) * (-1)) := by
        ring
    _ = -(-1 : ZMod p) := by
        rw [h]
    _ = 1 := by
        ring

/-- The manuscript's "valid tetrad" lemma.

The four values are

`1`, `q`, `p - 2`, `p - 1 - q`.

The excluded equalities `p = q + 2` and `p = 2*q + 1` are precisely
what prevents collisions among these four numbers. -/
def Good (p n : ℕ) : Prop :=
  1 ≤ n ∧
  n ≤ p - 1 ∧
  (((n.factorial : ℕ) : ZMod p) = 1)

def PairwiseDistinct4 (a b c d : ℕ) : Prop :=
  a ≠ b ∧ a ≠ c ∧ a ≠ d ∧
  b ≠ c ∧ b ≠ d ∧ c ≠ d

def HasTetrad (p : ℕ) : Prop :=
  Nat.Prime p ∧
    ∃ a b c d : ℕ,
      PairwiseDistinct4 a b c d ∧
      Good p a ∧ Good p b ∧ Good p c ∧ Good p d

lemma valid_tetrad
    {p q : ℕ}
    (hp : Nat.Prime p)
    (hq_ge : 3 ≤ q)
    (hq_odd : Odd q)
    (hq_gap : q + 2 ≤ p)
    (hq_fac : ((q.factorial : ℕ) : ZMod p) = 1)
    (hp_ne_q_add_two : p ≠ q + 2)
    (hp_ne_two_q_add_one : p ≠ 2 * q + 1) :
    HasTetrad p := by

  have hdistinct :
      PairwiseDistinct4 1 q (p - 2) (p - 1 - q) := by
    unfold PairwiseDistinct4
    constructor
    · omega
    constructor
    · omega
    constructor
    · intro h
      apply hp_ne_q_add_two
      omega
    constructor
    · intro h
      apply hp_ne_q_add_two
      omega
    constructor
    · intro h
      apply hp_ne_two_q_add_one
      omega
    · omega

  have hg1 : Good p 1 := by
    unfold Good
    constructor
    · omega
    constructor
    · omega
    · simp

  have hgq : Good p q := by
    unfold Good
    constructor
    · omega
    constructor
    · omega
    · exact hq_fac

  have hgp2 : Good p (p - 2) := by
    unfold Good
    constructor
    · omega
    constructor
    · omega
    · have h1_odd : Odd (1 : ℕ) := by
        norm_num

      have h1_le : 1 ≤ p - 1 := by
        omega

      have h1_fac : (((1 : ℕ).factorial : ℕ) : ZMod p) = 1 := by
        simp

      have hsym :
          (((p - 1 - 1).factorial : ℕ) : ZMod p) = 1 :=
        wilson_symmetry hp h1_le h1_odd h1_fac

      have hsub : p - 1 - 1 = p - 2 := by
        omega

      simpa [hsub] using hsym

  have hgpq : Good p (p - 1 - q) := by
    unfold Good
    constructor
    · omega
    constructor
    · omega
    · have hq_le : q ≤ p - 1 := by
        omega

      exact wilson_symmetry hp hq_le hq_odd hq_fac

  exact ⟨hp, 1, q, p - 2, p - 1 - q,
    hdistinct, hg1, hgq, hgp2, hgpq⟩
/-- Main theorem, unbounded form.

This is usually the best Lean form of “there are infinitely many such primes”. -/
theorem infinitely_many_tetrad_primes_unbounded :
    ∀ N : ℕ, ∃ p : ℕ, N < p ∧ HasTetrad p := by
  intro N

  let t := N + 1
  let q := 6 * t + 1

  have ht_pos : 1 ≤ t := by
    omega

  have hq_odd : Odd q := by
    refine ⟨3 * t, ?_⟩
    omega

  have hq_ge : 3 ≤ q := by
    omega

  have hNq : N < q := by
    omega

  have hq_add_two_not_prime : ¬ Nat.Prime (q + 2) := by
    have hcomp : ¬ Nat.Prime (3 * (2 * t + 1)) :=
      Nat.not_prime_mul (by norm_num) (by omega)
    have heq : q + 2 = 3 * (2 * t + 1) := by
      omega
    rw [heq]
    exact hcomp

  have htwo_q_add_one_not_prime : ¬ Nat.Prime (2 * q + 1) := by
    have hcomp : ¬ Nat.Prime (3 * (4 * t + 1)) :=
      Nat.not_prime_mul (by norm_num) (by omega)
    have heq : 2 * q + 1 = 3 * (4 * t + 1) := by
      omega
    rw [heq]
    exact hcomp

  have hlarge : 1 < q.factorial - 1 := by
    have hfact_ge_six : 6 ≤ q.factorial := by
      have h : (3 : ℕ).factorial ≤ q.factorial :=
        Nat.factorial_le hq_ge
      norm_num at h
      exact h
    omega

  obtain ⟨p, hp, hp_dvd⟩ :=
    Nat.exists_prime_and_dvd (n := q.factorial - 1) (by omega)

  obtain ⟨m, hm⟩ := hp_dvd

  have hfac_eq : q.factorial = p * m + 1 := by
    have hfac_pos : 1 ≤ q.factorial :=
      Nat.succ_le_of_lt (Nat.factorial_pos q)
    calc
      q.factorial = q.factorial - 1 + 1 := by
        omega
      _ = p * m + 1 := by
        rw [hm]

  have hq_fac : ((q.factorial : ℕ) : ZMod p) = 1 := by
    rw [hfac_eq]
    simp

  have hq_lt_p : q < p := by
    by_contra hnot
    have hp_le_q : p ≤ q := by
      omega

    have hp_dvd_fac : p ∣ q.factorial :=
      (Nat.Prime.dvd_factorial hp).2 hp_le_q

    have hzero : ((q.factorial : ℕ) : ZMod p) = 0 := by
      rcases hp_dvd_fac with ⟨a, ha⟩
      rw [ha]
      simp

    haveI : Fact (Nat.Prime p) := ⟨hp⟩
    have hne : (0 : ZMod p) ≠ 1 := zero_ne_one

    exact hne (hzero.symm.trans hq_fac)

  have hp_ne_q_add_one : p ≠ q + 1 := by
    intro hp_eq
    have hcomp : ¬ Nat.Prime (2 * (3 * t + 1)) :=
      Nat.not_prime_mul (by norm_num) (by omega)
    have heq : p = 2 * (3 * t + 1) := by
      rw [hp_eq]
      omega
    rw [heq] at hp
    exact hcomp hp

  have hq_gap : q + 2 ≤ p := by
    omega

  have hp_ne_q_add_two : p ≠ q + 2 := by
    intro hp_eq
    exact hq_add_two_not_prime (hp_eq ▸ hp)

  have hp_ne_two_q_add_one : p ≠ 2 * q + 1 := by
    intro hp_eq
    exact htwo_q_add_one_not_prime (hp_eq ▸ hp)

  refine ⟨p, ?_, ?_⟩
  · exact lt_trans hNq hq_lt_p
  · exact valid_tetrad hp hq_ge hq_odd hq_gap hq_fac
      hp_ne_q_add_two hp_ne_two_q_add_one

end Tetrads

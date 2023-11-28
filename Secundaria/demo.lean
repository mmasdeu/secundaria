import Mathlib.Tactic
import Mathlib.Data.Finsupp.Defs
import Mathlib.Init.Function
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Data.Rat.Lemmas
import Mathlib.Algebra.Group.Units
import Verbose

open Function Finset Dvd Rat
open scoped BigOperators

lemma induccio (P : ℕ → Prop) (h0 : P 0)
(h : ∀ n, (P n → P (n+1))) : ∀ n, P n := by sorry

/-
====================================================================
-/


lemma even_of_even_sq {m : ℕ} (h : 2 ∣ (m^2)) : 2 ∣ m := by
  -- This follows easily from knowing that 2 is prime.
  -- Let's make Lean aware of that:
  have prime_two : Prime 2 := Nat.prime_iff.mp Nat.prime_two
  sorry



lemma sqrt2_irrational (coprime_mn : m.gcd n = 1) : m^2 ≠ 2 * n^2 := by
  -- 1) Fem una demostració per reducció a l'absurd
  -- 2) Com que m^2 = 2 * (...), deduïm que 2 ∣ m
  -- 3) Veiem que 2 ∣ n
  -- 4) Deduïm dels dos punts anteriors que 2 ∣ gcd(m,n)
  -- 5) Contradicció amb la hipòtesi inicial
  sorry
  done





















/-
====================================================================
-/

example : ∀ n, ∑ k in range (n + 1), (k : ℝ) = n * (n + 1) / 2 := by
  sorry
  done












/-
====================================================================
-/











example (A : Type) [CommRing A] [IsDomain A] (p : A) (hp : p ≠ 0)
  (h : ∀ a b, p ∣ a * b → p ∣ a ∨ p ∣ b) :
  ∀ (a b : A), p = a*b → IsUnit a ∨ IsUnit b := by
  intro a b hab
  have H : p ∣ a * b := by exact Eq.dvd hab
  apply h at H
  wlog h1 : p ∣ a generalizing a b
  · rw [Or.comm] at H ⊢
    rw [mul_comm] at hab
    apply this b a hab H (by tauto)
  right
  obtain ⟨k, hk⟩ := h1
  subst a
  rw [mul_assoc] at hab
  nth_rewrite 1 [←mul_one p] at hab
  have hab' : 1 = k * b
  · exact (mul_right_inj' hp).mp hab
  rw [isUnit_iff_exists_inv]
  use k
  rw [hab']
  ring
  done


















/-
====================================================================
-/


Exemple "Exercici del Parcial 2024"
  Dades:
  Hipòtesis:
  Conclusió: ∀ n, ∃ m, ∀ k, ( (k > n) → 2*k > n + m )

Demostració:
  Sigui n : ℕ
  Vegem que 1 funciona
  Sigui k > n
  Es conclou amb k_gt
QED














def Fib : ℕ → ℕ
| 0 => 0
| 1 => 1
| (n + 2) => Fib n + Fib (n+1)

@[simp] lemma Fib0 : Fib 0 = 0 := rfl
@[simp] lemma Fib1 : Fib 1 = 1 := rfl
@[simp] lemma Fibdef (n : ℕ) : Fib (n+2) = Fib n + Fib (n+1) := by rfl

Exemple "Exercici sobre Fibonacci"
  Conclusió: ∀ n, 1 + ∑ i in range n, Fib i = Fib (n+1)

Demostració:
  Apliquem induccio
  · norm_num
  · Sigui n
    Suposem hn
    Es reescriu mitjançant range_succ
    Es reescriu mitjançant sum_insert not_mem_range_self
    Es reescriu mitjançant Fibdef
    Es reescriu mitjançant ← hn
    Es calcula
QED


section Funcions

variable {X Y Z : Type}
variable (f : X → Y) (g : Y → Z)

lemma Comp_def {x : X} : (g ∘ f) x = g (f x) := rfl
lemma Injective_def : Injective f ↔ ∀ x y, f x = f y → x = y := Iff.rfl
lemma Surjective_def : Surjective f ↔ ∀ y, ∃ x, f x  = y := Iff.rfl

Exemple "Composició injectiva"
  Dades: (f : X → Y) (g : Y → Z)
  Hipòtesis: (h : Injective (g ∘ f))
  Conclusió: Injective f

Demostració:
  Es reescriu mitjançant Injective_def at h ⊢
  Sigui x y
  Suposem hf
  Apliquem h
  Es reescriu mitjançant Comp_def
  Es reescriu mitjançant Comp_def
  Es reescriu mitjançant hf
QED


Exemple "Composició exhaustiva"
  Dades: (f : X → Y) (g : Y → Z)
  Hipòtesis: (h : Surjective (g ∘ f))
  Conclusió: Surjective g

Demostració:
  Es reescriu mitjançant Surjective_def at h ⊢
  Sigui b
  Per h b s'obté x tal que hx
  Es reescriu mitjançant Comp_def at hx
  Vegem que (f x) funciona
  trivial
QED


def Collatz : ℕ → ℕ := λ n ↦ if (Even n) then n / 2  else 3 * n + 1


Exemple "Collatz no és injectiva"
  Conclusió: ¬ (Injective Collatz)

Demostració:
  Es reescriu mitjançant Injective_def
  push_neg
  Vegem que 1 funciona
  Vegem que 8 funciona
  Afirmació h : Even 8 de Nat.even_iff.mpr rfl
  simp [Collatz, h]
  Es calcula
QED



Exemple "Collatz és exhaustiva'"
  Conclusió: Surjective Collatz
Demostració:
  Es reescriu mitjançant Surjective_def
  Sigui b : ℕ
  Vegem que 2*b funciona
  simp [Collatz]
QED


end Funcions
























/-
====================================================================
-/

/-
====================================================================
-/

/-
====================================================================
-/


Exemple "L'arrel quadrada de 2 és irracional"
  Dades: (m n : ℕ)
  Hipòtesis: (mn_coprimers : m.gcd n = 1)
  Conclusió:  m^2 ≠ 2 * n^2

Demostració:
  Suposem per reducció a l'absurd que hc : m^2 = 2 * n^2

  Afirmació m_es_parell : 2 ∣ m perquè
    Apliquem even_of_even_sq
    Vegem que n^2 funciona
    trivial

  Afirmació n_es_parell : 2 ∣ n perquè
    Apliquem even_of_even_sq
    Per m_es_parell obtenim k tal que h : m = 2 * k
    Vegem que k^2 funciona
    Es reescriu mitjançant h at hc
    linarith

  Afirmació mcd_es_parell : 2 ∣ Nat.gcd m n de
    Nat.dvd_gcd m_es_parell n_es_parell

  Es reescriu mitjançant mn_coprimers at mcd_es_parell
  trivial
QED




example (coprime_mn : m.gcd n = 1) : m^2 ≠ 2 * n^2 := by
  -- we do a proof by contradiction
  by_contra hc

  -- since m^2 = 2 * something, deduce that m is even
  have even_m : 2 ∣ m
  · sorry

  -- Show that n is even, using that n^2 is
  have even_n : 2 ∣ n
  · apply even_of_even_sq
      -- Write m as 2 * k
    obtain ⟨k, mek⟩ := even_m
    use k^2
    rw [mek] at hc
    linarith

  -- Deduce that 2 ∣ gcd(m,n)
  have even_gcd : 2 ∣ Nat.gcd m n
  · sorry

  -- Get a contradiction somehow
  rw [coprime_mn] at even_gcd
  simp at even_gcd


lemma sqrt2_irrational' {x : ℚ} (hpos : 0 ≤ x) : x^2 ≠ 2 := by
  -- We do a proof by contradiction
  by_contra hc

  -- The numerator and denominator of x are coprime
  have num_den_coprime := Rat.reduced x
  apply sqrt2_irrational num_den_coprime

  -- The numerator is positive and the denominator is nonzero
  have num_pos : 0 ≤ x.num := by sorry
  have h1 : x.num.natAbs = x.num := by sorry
  have denom_ne_zero : x.den ≠ 0 := by sorry

  rw [←num_div_den x] at hc
  field_simp at hc
  rw [←h1] at hc
  norm_cast at hc

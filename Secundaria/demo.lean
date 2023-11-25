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

variable {X Y Z : Type}

lemma even_of_even_sq {m : ℕ} (h : 2 ∣ (m^2)) : 2 ∣ m := by
  -- This follows easily from knowing that 2 is prime. Let's make Lean aware of that:
  have prime_two : Prime 2 := Nat.prime_iff.mp Nat.prime_two
  sorry


lemma sqrt2_irrational_aux (coprime_mn : m.gcd n = 1) : m^2 ≠ 2 * n^2 := by
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


lemma sqrt2_irrational {x : ℚ} (hpos : 0 ≤ x) : x^2 ≠ 2 := by
  -- We do a proof by contradiction
  by_contra hc

  -- The numerator and denominator of x are coprime
  have num_den_coprime := Rat.reduced x
  apply sqrt2_irrational_aux num_den_coprime

  -- The numerator is positive and the denominator is nonzero
  have num_pos : 0 ≤ x.num := by sorry
  have h1 : x.num.natAbs = x.num := by sorry
  have denom_ne_zero : x.den ≠ 0 := by sorry

  rw [←num_div_den x] at hc
  field_simp at hc
  rw [←h1] at hc
  norm_cast at hc





























lemma Comp_def {x : X} (f : X → Y) (g : Y → Z) : (g ∘ f) x = g (f x) := by rfl
lemma Injective_def (f : X → Y) : Injective f ↔ ∀ x y, f x = f y → x = y := by rfl
lemma Surjective_def (f : X → Y) : Surjective f ↔ ∀ y, ∃ x, f x  = y := by rfl

example (f : X → Y) (g : Y → Z) : Injective (g ∘ f) → Injective f := by
  intro h x y hxy
  rw [Injective_def] at h
  apply h
  rw [Comp_def, Comp_def, hxy]
  done

example (f : X → Y) (g : Y → Z) : Surjective (g ∘ f) → Surjective g := by
  intro h
  rw [Surjective_def] at h ⊢
  intro b
  cases' h b with x hx
  rw [Comp_def] at hx
  use f x


















example (n : ℕ) : ∑ k in range (n + 1), (k : ℝ) = n * (n + 1) / 2 := by
  induction' n with d hd
  · simp
  · rw [range_succ]
    rw [sum_insert not_mem_range_self]
    rw [hd]
    field_simp
    ring





















example (n : ℕ) : ∑ k in range (n + 1), (k*k : ℝ) = n*(n + 1)*(2*n + 1) / 6 := by
  induction' n with d hd
  · simp
  · rw [range_succ]
    rw [sum_insert not_mem_range_self]
    rw [hd]
    field_simp
    ring





example (A : Type) [CommRing A] [IsDomain A] (p : A) (hp : p ≠ 0) (h : ∀ a b, p ∣ a * b → p ∣ a ∨ p ∣ b) :
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
  have hab' : 1 = k*b
  · aesop
  rw [isUnit_iff_exists_inv]
  use k
  rw [hab']
  ring
  done
















-- Fibonacci

lemma induction_one (P : ℕ → Prop) (h0 : P 0)
(h : ∀ n, (P n → P (n+1))) : ∀ n, P n := by
  intro n
  induction' n with d hd
  · exact h0
  · exact h d hd

lemma induction_two (P : ℕ → Prop) (h0 : P 0) (h1 : P 1)
(h : ∀ n, (P n → P (n+1) → P (n+2))) : ∀ n, P n := by
  suffices : ∀ n, P n ∧ P (n+1)
  · exact λ n ↦ (this n).1
  intro n
  induction' n with d hd
  exact ⟨h0, h1⟩
  specialize h d hd.1 hd.2
  exact ⟨hd.2, h⟩

def Fib : ℕ → ℕ
| 0 => 0
| 1 => 1
| (n + 2) => Fib n + Fib (n+1)

@[simp] lemma Fib0 : Fib 0 = 0 := rfl
@[simp] lemma Fib1 : Fib 1 = 1 := rfl
@[simp] lemma Fibdef (n : ℕ) : Fib (n+2) = Fib n + Fib (n+1) := rfl

example : ∀ n, ∀ k, Fib (n + k + 1) = (Fib k) * (Fib n) + (Fib (k+1)) * (Fib (n+1)) := by
  intro n
  apply induction_two
  · norm_num
  · norm_num
  · intro k h0 h1
    rw [show n+(k+2)+1 = (n+k+1)+2 by ring]
    rw [Fibdef]
    rw [show n + k + 1 + 1 = n + (k+1) + 1 by ring]
    rw [h0, h1]
    simp only [Fibdef]
    ring



















-- Parcial 2024

example : ∀ n, ∃ m, ∀ k, ( (k > n) → 2*k > n + m ) := by
  intro n
  use 1
  intro k hk
  linarith
  done














example : ∀ n, 1 + ∑ i in range n, Fib i = Fib (n+1) := by
  apply induction_one
  · norm_num
  · intro n hn
    rw [range_succ]
    rw [sum_insert not_mem_range_self]
    rw [Fibdef]
    rw [←hn]
    linarith
  done

def Collatz : ℕ → ℕ := λ n ↦ if (Even n) then n / 2  else 3 * n + 1

example : ¬ (Injective Collatz) := by
  simp [Injective]
  use 1, 8
  have : Even 8 := by exact Nat.even_iff.mpr rfl
  simp [Collatz, this]
  norm_num
  done

example : Surjective Collatz := by
  simp [Surjective]
  intro b
  use 2 * b
  simp [Collatz]
  done
























Exemple "L'arrel quadrada de 2 és irracional"

  Dades: (m n : ℕ)
  Hipòtesis: (mn_coprimers : m.gcd n = 1)
  Conclusió:  m^2 ≠ 2 * n^2

Demostració:

  Suposem per reducció a l'absurd que hc : m^2 = 2 * n^2

  Afirmació m_es_parell : 2 ∣ m per
    Apliquem even_of_even_sq
    Vegem que n^2 funciona
    trivial

  -- Demostrem que n is parell fent servir que n^2 ho és
  Afirmació n_es_parell : 2 ∣ n per
    Apliquem even_of_even_sq
    Per m_es_parell obtenim k tal que h : m = 2 * k
    Vegem que k^2 funciona
    Es reescriu mitjançant h at hc
    linarith

  Afirmació mcd_es_parell : 2 ∣ Nat.gcd m n de
    Nat.dvd_gcd m_es_parell n_es_parell

  -- Obtenim una contradicció
  Es reescriu mitjançant mn_coprimers at mcd_es_parell
  trivial

QED

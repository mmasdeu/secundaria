import Mathlib.Tactic
import Mathlib.Data.Finsupp.Defs

open Multiset
open scoped BigOperators
set_option autoImplicit false
set_option pp.proofs.withType false
set_option maxHeartbeats 400000
variable {X : Type} [Fintype X] [DecidableEq X]

@[ext]
structure Ballot (X : Type) where
  carrier : List X
  nodup : carrier.Nodup

@[ext]
lemma BallotEq {b1 b2 : Ballot X} (h : b1.carrier = b2.carrier) : b1 = b2 := by
  ext n a
  simp [h]

-- @[simp]
lemma BallotEq' {b1 b2 : Ballot X} :  b1 = b2 ↔ b1.carrier = b2.carrier:= ⟨fun h => by simp [h], BallotEq⟩

@[coe]
def Ballot.ofList (l : List X) (h : l.Nodup) : Ballot X := ⟨l, h⟩

@[coe]
def Ballot.ofSingleton (x : X) : Ballot X := ⟨[x], List.nodup_singleton x⟩

instance HasCoeSingleton : Coe X (Ballot X) := ⟨Ballot.ofSingleton⟩

@[simp] lemma Ballot.ofSingleton_carrier (x : X) : (Ballot.ofSingleton x).carrier = [x] := rfl


def Ballot.ofPair (x y : X) (hxy : x ≠ y := by simp) : Ballot X := ⟨[x, y], by simp [List.Nodup, hxy]⟩
@[simp] lemma Ballot.ofPair_carrier (x y : X) (hxy : x ≠ y) : (Ballot.ofPair x y hxy).carrier = [x,y] := rfl

instance : DecidableEq (Ballot X) := by
  intro x y
  rw [BallotEq']
  infer_instance


@[simp] lemma Ballot.eq_iff (x y : X) : Ballot.ofSingleton x = Ballot.ofSingleton y ↔ x = y := by simp [BallotEq']


@[simp] abbrev Election (X : Type) := Multiset (Ballot X)

instance : Singleton (Ballot X) (Multiset (Ballot X)) := ⟨fun a => a ::ₘ 0⟩
instance : Singleton X (Ballot X) := ⟨fun a => (Ballot.ofSingleton a : Ballot X)⟩

@[simp] lemma singleton_eq_of_singleton (x : X) : {x} = Ballot.ofSingleton x := rfl

@[simp] lemma singleton_ne_pair (x y : X) (hxy : x ≠ y) : Ballot.ofSingleton x ≠ Ballot.ofPair x y hxy := by
  simp [BallotEq']

def Method (X : Type) := Election X → X

def hasP1 (M : Method X) := ∀ {x : X}, ∀ E₁ E₂ : Election X, ∀ b : Ballot X,
  E₁ + {{x}} = E₂ + {b} → M E₁ = x → M E₂ = x

def hasP2 (M : Method X) := ∀ x y : X, ∀ hxy : x ≠ y,
∀ E₁ E₂ : Election X, E₁ + {Ballot.ofPair x y hxy} =  E₂ + {{x}} →
M E₁ = x → M E₂ = x

def hasP3 (M : Method X) := ∀ {E : Election X}, ∀ {x : X},
  (∀ b : Ballot X, b ∈ E → b.carrier.length = 1) →
  (∀ y : X, y ≠ x → (count {y} E) < (count {x} E)) → M E = x

def hasP4 (M : Method X) := ∀ {x y : X}, (hxy : x ≠ y) → ∀ E : Election X,
  card E < 2 * (count (Ballot.ofPair x y hxy) E) + 2 * (count (Ballot.ofPair y x hxy.symm) E) → M E = x ∨ M E = y

def hasP1' (M : Method X) := ∀ k : ℕ, ∀ {x : X}, ∀ E₁ E₂ : Election X, ∀ b : Ballot X,
  E₁ + k • {Ballot.ofSingleton x} = E₂ + k • {b} → M E₁ = x → M E₂ = x

def hasP2' (M : Method X) := ∀ k : ℕ, ∀ x y : X, ∀ hxy : x ≠ y,
∀ E₁ E₂ : Election X, E₁ + k • {Ballot.ofPair x y hxy} =  E₂ + k • {Ballot.ofSingleton x} →
M E₁ = x → M E₂ = x

macro "multiset_add" : tactic => `(tactic|(rw [ext]; intro x; simp [*]; ring))

lemma add_tsub_cancel_left' (a b c : Multiset X) : a + b + c - b = a + c := by
  rw [tsub_eq_of_eq_add_rev _]
  rw [add_left_comm, add_assoc]

lemma add_succ_cancel_left (k : ℕ) (a b : Multiset X) : a + (k+1) • b - k • b = a + b := by
  rw [tsub_eq_of_eq_add]
  rw [add_assoc]
  congr

lemma aux (E : Election X) (c : Ballot X) (k : ℕ) : k • {c} ≤ E ↔ k ≤ count c E := by
  simp [le_iff_count, count_singleton]
  constructor
  · intro h
    simpa using h c
  · intro h a
    by_cases hac : a = c <;> (simp at hac; simp [hac, h])
  done

lemma leq_smul_singleton {E₁ E₂ : Election X} {b c : Ballot X} {k: ℕ} (h : E₁ + k • {b} = E₂ + k • {c}) (hbc : c ≠ b) :
k • {c} ≤ E₁ := by
  rw [aux]
  rw [ext] at h
  specialize h c
  simp [hbc] at h
  simp [h]

lemma hasP1'_of_hasP1 (M : Method X) (h : hasP1 M) : hasP1' M := by
  intro k
  induction k with
  | zero => simp
  | succ k hI =>
      intro x E₁ E₂ b hh hE₁
      let E₃ := E₁ + k • {{x}} - k • {b}
      specialize @hI x E₁ E₃ b
      have h3 : M E₃ = x
      · apply hI _ hE₁
        simp [E₃]
        refine (tsub_add_cancel_of_le ?h3.a.h).symm
        by_cases hx : b = Ballot.ofSingleton x
        · simp [hx, Multiset.le_add_left]
        · calc
          k • {b} ≤ (k + 1) • {b} := by (simp [le_iff_count]; exact (fun x => by linarith))
          _ ≤ E₁ := leq_smul_singleton hh (by tauto)
          _ ≤ E₁ + k • {{x}} := by exact Multiset.le_add_right E₁ (k • {{x}})
      apply h E₃ E₂ b _ h3
      simp [E₃]
      have : E₁ + k • {Ballot.ofSingleton x} - k • {b} + {Ballot.ofSingleton x} = E₁ + k • {Ballot.ofSingleton x}
        + {Ballot.ofSingleton x} - k • {b}
      · by_cases hbx : b = Ballot.ofSingleton x
        · simp [hbx, add_tsub_cancel_left']
        · simp [hbx]; ext c; by_cases hc : c = b <;> (simp at hc hbx; simp [hc, hbx])
      rw [this, add_assoc,←succ_nsmul',hh, add_succ_cancel_left]

lemma hasP2'_of_hasP2 (M : Method X) (h : hasP2 M) : hasP2' M := by
  intro k
  induction k with
  | zero => simp
  | succ k hI =>
      intro x y hxy E₁ E₂ hh hE₁
      let E₃ := E₁ + k • {Ballot.ofPair x y hxy} - k • {{x}}
      specialize @hI x y hxy E₁ E₃
      have h3 : M E₃ = x
      simp [E₃]
      · apply hI _ hE₁
        refine (tsub_add_cancel_of_le ?_).symm
        calc
        _ ≤ (k + 1) • {{x}} := by (simp [le_iff_count]; exact fun x => by linarith)
        _ ≤ E₁ := leq_smul_singleton hh (by simp [hxy])
        _ ≤ E₁ + k • {Ballot.ofPair x y hxy} := by apply Multiset.le_add_right
      apply h x y hxy E₃ E₂ _ h3
      have : E₁ + k • {Ballot.ofPair x y hxy} - k • {Ballot.ofSingleton x} + {Ballot.ofPair x y hxy} = E₁ + k • {Ballot.ofPair x y hxy}
        + {Ballot.ofPair x y hxy} - k • {Ballot.ofSingleton x}
      · ext c; by_cases hc : c = Ballot.ofSingleton x <;> (simp at hc; simp [hc])
      simp [E₃]
      rw [this, add_assoc,←succ_nsmul',hh, add_succ_cancel_left]

macro "majority" : tactic => `(tactic| (intro i hi; fin_cases i <;> try{ simp [BallotEq'] at *} ; try {aesop}))-- [BallotEq'] at *))
lemma fin3 (x : Fin 3) : x = 0 ∨ x = 1 ∨ x = 2 := by fin_cases x <;> decide
@[simp] lemma Fin.ext_iff' (a b : Fin 3) : a = b ↔ a.val = b.val := Fin.ext_iff

abbrev b0 : Ballot (Fin 3) := {0}
abbrev b1 : Ballot (Fin 3) := {1}
abbrev b2 : Ballot (Fin 3) := {2}
abbrev b01 : Ballot (Fin 3) := Ballot.ofPair (0 : Fin 3) 1
abbrev b10 : Ballot (Fin 3) := Ballot.ofPair (1 : Fin 3) 0

abbrev EE := Election (Fin 3)
abbrev αP : EE := 11 • {b0}  + 10 • {b1}  + 10 • {b2}
abbrev αQ : EE := 11 • {b0}  +  8 • {b1}  + 12 • {b2}
abbrev αP': EE := 10 • {b0}  + 11 • {b1}  + 10 • {b2}
abbrev αQ': EE :=  8 • {b0}  + 11 • {b1}  + 12 • {b2}
abbrev βP : EE := 11 • {b01} + 10 • {b1}  + 10 • {b2}
abbrev βQ : EE := 11 • {b01} +  8 • {b1}  + 12 • {b2}
abbrev βR : EE :=  8 • {b01} +  8 • {b1}  + 15 • {b2}
abbrev β'P':EE := 10 • {b0}  + 11 • {b10} + 10 • {b2}
abbrev β'Q':EE :=  8 • {b0}  + 11 • {b10} + 12 • {b2}
abbrev β'R :EE :=  8 • {b0}  +  8 • {b10} + 15 • {b2}
abbrev γR  :EE :=  8 • {b01} +  8 • {b10} + 15 • {b2}



theorem Woodall (M : Method (Fin 3)) (h1 : hasP1 M) (h2 : hasP2 M) (h3 : hasP3 M) (h4: hasP4 M) : False := by
  replace h1 : hasP1' M := hasP1'_of_hasP1 M h1
  replace h2 : hasP2' M := hasP2'_of_hasP2 M h2
  have h5 : M αP   = 0 := h3 (by aesop) (by majority)
  have h5': M αP'  = 1 := h3 (by aesop) (by majority)
  have h6 : M αQ   = 2 := h3 (by aesop) (by majority)
  have h6': M αQ'  = 2 := h3 (by aesop) (by majority)
  have h7 : M βP   = 0 := (h2 11 0 1 (by norm_num) αP βP (by multiset_add)) h5
  have h7': M β'P' = 1 := (h2 11 1 0 (by norm_num) αP' β'P' (by multiset_add)) h5'
  rcases (fin3 (M βQ)) with h8 | h8 | h8
  · rw [h1 11 βQ αQ b01 (by multiset_add) h8] at h6; contradiction
  · rw [h1 2 βQ βP b2 (by multiset_add) h8] at h7; contradiction
  rcases fin3 (M β'Q') with h8' | h8' | h8'
  · rw [h1 2 β'Q' β'P' b2 (by multiset_add) h8'] at h7'; contradiction
  · rw [h1 11 β'Q' αQ' b10 (by multiset_add) h8'] at h6'; contradiction
  have h9 : M βR  = 2 := h1 3 βQ βR b01 (by multiset_add) (by tauto)
  have h9': M β'R = 2 := h1 3 β'Q' β'R b10 (by multiset_add) (by tauto)
  have hc : M γR = 0 ∨ M γR = 1
  · apply h4 (by norm_num)
    rw [show card γR = 31 by norm_num]; simp [BallotEq']
  rcases hc with hh | hh
  · rw [h1 8 γR β'R b01 (by multiset_add) hh] at h9'; contradiction
  · rw [h1 8 γR βR b10 (by multiset_add) hh] at h9; contradiction

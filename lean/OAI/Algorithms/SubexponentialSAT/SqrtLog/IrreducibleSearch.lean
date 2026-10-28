import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearchBasic

namespace OAI.Algorithms

/-!
# Executable arbitrary-degree irreducible search over F₃

Search all monic degree-`d` coefficient vectors and reject each candidate
which is the product of two nonconstant arrays of degree at most `d`.
The test uses explicit convolution. Mathematical finite-field existence
proves that the executable search succeeds for every positive `d`.
-/
namespace SubexponentialSAT.SqrtLog.IrreducibleSearch

open Polynomial

instance primeThree : Fact (Nat.Prime 3) := ⟨by decide⟩

def candidates (d : ℕ) : List (Fin d → F) :=
  QuarticSearch.vectors (QuarticSearch.elements 3) d

theorem mem_candidates (d : ℕ) (c : Fin d → F) : c ∈ candidates d :=
  QuarticSearch.mem_vectors _ (QuarticSearch.mem_elements 3) d c

@[simp] theorem length_candidates (d : ℕ) : (candidates d).length = 3 ^ d := by
  simp [candidates, QuarticSearch.length_vectors]

def factorPairs (d : ℕ) : List ((Fin (d + 1) → F) × (Fin (d + 1) → F)) :=
  (candidates (d + 1)).flatMap fun a => (candidates (d + 1)).map fun b => (a, b)

theorem mem_factorPairs (d : ℕ) (a b : Fin (d + 1) → F) : (a, b) ∈ factorPairs d := by
  apply List.mem_flatMap.mpr
  exact ⟨a, mem_candidates _ _, List.mem_map.mpr ⟨b, mem_candidates _ _, rfl⟩⟩

@[simp] theorem length_factorPairs (d : ℕ) :
    (factorPairs d).length = 3 ^ (2 * (d + 1)) := by
  simp [factorPairs, List.length_flatMap, ← pow_two, ← pow_mul, Nat.mul_comm]

def pairPass {d : ℕ} (c : Fin d → F)
    (ab : (Fin (d + 1) → F) × (Fin (d + 1) → F)) : Bool :=
  !(nonconstant ab.1 && nonconstant ab.2 && productEq c ab.1 ab.2)

theorem pairPass_iff {d : ℕ} (c : Fin d → F) (a b : Fin (d + 1) → F) :
    pairPass c (a, b) = true ↔
      ¬(0 < (Polynomial.ofFn (d + 1) a).natDegree ∧
        0 < (Polynomial.ofFn (d + 1) b).natDegree ∧
        Polynomial.ofFn (d + 1) a * Polynomial.ofFn (d + 1) b = QuarticSearch.poly c) := by
  rw [← nonconstant_iff (Nat.succ_pos d), ← nonconstant_iff (Nat.succ_pos d),
    ← productEq_iff]
  unfold pairPass
  cases nonconstant a <;> cases nonconstant b <;> cases productEq c a b <;> decide

def passes {d : ℕ} (c : Fin d → F) : Bool := (factorPairs d).all (pairPass c)

theorem passes_iff {d : ℕ} (hd : 0 < d) (c : Fin d → F) :
    passes c = true ↔ Irreducible (QuarticSearch.poly c) := by
  rw [passes, List.all_eq_true]
  constructor
  · intro h
    refine ⟨Polynomial.not_isUnit_of_natDegree_pos _ (by simpa using hd), ?_⟩
    intro a b hab
    by_cases ha : IsUnit a
    · exact Or.inl ha
    by_cases hb : IsUnit b
    · exact Or.inr hb
    exfalso
    have hprod : a * b ≠ 0 := by rw [← hab]; exact (QuarticSearch.poly_monic c).ne_zero
    have ha0 : a ≠ 0 := left_ne_zero_of_mul hprod
    have hb0 : b ≠ 0 := right_ne_zero_of_mul hprod
    have hdeg : a.natDegree + b.natDegree = d := by
      rw [← Polynomial.natDegree_mul ha0 hb0, ← hab, QuarticSearch.poly_natDegree]
    have hap : 0 < a.natDegree :=
      Polynomial.natDegree_pos_of_not_isUnit_of_dvd_monic
        (QuarticSearch.poly_monic c) ha ⟨b, hab⟩
    have hbp : 0 < b.natDegree :=
      Polynomial.natDegree_pos_of_not_isUnit_of_dvd_monic
        (QuarticSearch.poly_monic c) hb ⟨a, by rw [mul_comm]; exact hab⟩
    let av := Polynomial.toFn (d + 1) a
    let bv := Polynomial.toFn (d + 1) b
    have hav : Polynomial.ofFn (d + 1) av = a :=
      Polynomial.ofFn_comp_toFn_eq_id_of_natDegree_lt (by omega)
    have hbv : Polynomial.ofFn (d + 1) bv = b :=
      Polynomial.ofFn_comp_toFn_eq_id_of_natDegree_lt (by omega)
    have hp := (pairPass_iff c av bv).mp (h (av, bv) (mem_factorPairs d av bv))
    exact hp (by simpa only [hav, hbv] using And.intro hap (And.intro hbp hab.symm))
  · intro h ab _
    apply (pairPass_iff c ab.1 ab.2).mpr
    rintro ⟨ha, hb, hab⟩
    rcases h.isUnit_or_isUnit hab.symm with hu | hu
    · exact Polynomial.not_isUnit_of_natDegree_pos _ ha hu
    · exact Polynomial.not_isUnit_of_natDegree_pos _ hb hu

def evaluate {d : ℕ} (c : Fin d → F) : Bool × ℕ :=
  QuarticSearch.checkAll (pairPass c) (factorPairs d)

@[simp] theorem evaluate_value {d : ℕ} (c : Fin d → F) :
    (evaluate c).1 = passes c := QuarticSearch.checkAll_value _ _

theorem evaluate_count_le {d : ℕ} (c : Fin d → F) :
    (evaluate c).2 ≤ 3 ^ (2 * (d + 1)) := by
  simpa [evaluate] using QuarticSearch.checkAll_count_le (pairPass c) (factorPairs d)

/-- Result, number of candidate tests, number of factor-pair tests. -/
def search (d : ℕ) : Option (Fin d → F) × ℕ × ℕ :=
  QuarticSearch.scan evaluate (candidates d)

/-- Total coefficient selection; positivity proves that the default is unused. -/
def coefficients (d : ℕ) : Fin d → F := (search d).1.getD (fun _ => 0)

theorem search_candidates_le (d : ℕ) : (search d).2.1 ≤ 3 ^ d := by
  simpa [search] using QuarticSearch.scan_candidates_le evaluate (candidates d)

theorem search_tests_le (d : ℕ) : (search d).2.2 ≤ 3 ^ (3 * d + 2) := by
  have h := QuarticSearch.scan_tests_le evaluate (candidates d) (3 ^ (2 * (d + 1)))
    (fun c _ => evaluate_count_le c)
  simpa only [search, length_candidates, ← pow_add, show d + 2 * (d + 1) = 3 * d + 2 by omega]
    using h

theorem exists_passing {d : ℕ} (hd : 0 < d) : ∃ c ∈ candidates d, passes c = true := by
  obtain ⟨f, hm, hi, hn⟩ := SubexponentialSAT.FiniteField.exists_monic_irreducible 3 d (by omega)
  let c : Fin d → F := fun i => f.coeff i
  refine ⟨c, mem_candidates _ _, (passes_iff hd c).mpr ?_⟩
  simpa only [c, QuarticSearch.poly_of_coeff f hm hn] using hi

theorem search_ne_none {d : ℕ} (hd : 0 < d) : (search d).1 ≠ none := by
  intro hn
  have hh : (candidates d).find? (fun c => (evaluate c).1) = none := by
    simpa only [search, QuarticSearch.scan_value] using hn
  obtain ⟨c, hc, hp⟩ := exists_passing hd
  have hnop := List.find?_eq_none.mp hh c hc
  exact hnop (by simpa using hp)

theorem coefficients_irreducible {d : ℕ} (hd : 0 < d) :
    Irreducible (QuarticSearch.poly (coefficients d)) := by
  cases hs : (search d).1 with
  | none => exact False.elim (search_ne_none hd hs)
  | some c =>
      have hf : (candidates d).find? (fun c => (evaluate c).1) = some c := by
        simpa only [search, QuarticSearch.scan_value] using hs
      have hp := List.find?_some hf
      have hi := (passes_iff hd c).mp (by simpa using hp)
      simpa [coefficients, hs] using hi

theorem coefficients_monic (d : ℕ) : (QuarticSearch.poly (coefficients d)).Monic :=
  QuarticSearch.poly_monic _

theorem coefficients_natDegree (d : ℕ) :
    (QuarticSearch.poly (coefficients d)).natDegree = d := QuarticSearch.poly_natDegree _

def liftedCoefficients (d t : ℕ) : Fin d → ZMod (3 ^ t) :=
  fun i => ((coefficients d i).val : ZMod (3 ^ t))

end SubexponentialSAT.SqrtLog.IrreducibleSearch

end OAI.Algorithms

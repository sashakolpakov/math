import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.PerturbationProgramStored

namespace OAI.Algorithms

/-! Validity and exact denotation of the reversed, unnormalized coefficient
stream emitted by the new perturbation assembly. Zero coefficients remain. -/
namespace SubexponentialSAT.SqrtLog.PerturbationAssembly
open SubexponentialSAT.SubexpSymbolicCost
open _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.Squarefree Squarefree.Sparse PerturbationProgram
open scoped BigOperators

variable {C R : Type*} [CommRing R]

def rawWords {n : ℕ} (beta : C) (tails : Fin n → List C) :
    List (Index (Fin n) × C) :=
  ((Index.origin,beta) ::
    (List.ofFn fun v => coefficientRecords v 1 (tails v)).flatten).reverse

private theorem coefficient_mem {n : ℕ} (v : Fin n) (j : ℕ) (p : List C)
    (a : Index (Fin n) × C) (ha : a ∈ coefficientRecords v j p) :
    a.1.u = 0 ∧ j ≤ a.1.z ∧ a.1.z < j+p.length ∧ a.1.vars = {v} := by
  induction p generalizing j with
  | nil => simp [coefficientRecords] at ha
  | cons c cs ih =>
      rcases List.mem_cons.mp ha with h | h
      · subst a
        exact ⟨rfl,le_rfl,by simp,rfl⟩
      · obtain ⟨hu,hlo,hhi,hv⟩ := ih (j+1) h
        exact ⟨hu,by omega,by simp only [List.length_cons]; omega,hv⟩

private theorem coefficient_pairwise {n : ℕ} (v : Fin n) (j : ℕ) (p : List C) :
    (coefficientRecords v j p).Pairwise (fun a b => a.1 ≠ b.1) := by
  induction p generalizing j with
  | nil => simp [coefficientRecords]
  | cons c cs ih =>
      apply List.pairwise_cons.mpr
      constructor
      · intro a ha he
        have hz := (coefficient_mem v (j+1) cs a ha).2.1
        have hez := congrArg Index.z he
        simp only at hez
        omega
      · exact ih (j+1)

private theorem rows_pairwise {n : ℕ} (tails : Fin n → List C)
    (vs : List (Fin n)) (hv : vs.Nodup) :
    (vs.flatMap fun v => coefficientRecords v 1 (tails v)).Pairwise
      (fun a b => a.1 ≠ b.1) := by
  induction vs with
  | nil => simp
  | cons v vs ih =>
      obtain ⟨hn,ht⟩ := List.nodup_cons.mp hv
      apply List.pairwise_append.mpr
      refine ⟨coefficient_pairwise v 1 (tails v),ih ht,?_⟩
      intro a ha b hb he
      obtain ⟨w,hw,hb⟩ := List.mem_flatMap.mp hb
      have hav := (coefficient_mem v 1 (tails v) a ha).2.2.2
      have hbw := (coefficient_mem w 1 (tails w) b hb).2.2.2
      have hevars := congrArg Index.vars he
      rw [hav,hbw] at hevars
      have hvw : v=w := by simpa using hevars
      exact hn (hvw.symm ▸ hw)

theorem rawWords_nodup {n : ℕ} (beta : C) (tails : Fin n → List C) :
    ((rawWords beta tails).map Prod.fst).Nodup := by
  rw [rawWords,List.map_reverse]
  apply List.nodup_reverse.mpr
  apply List.pairwise_map.mpr
  apply List.pairwise_cons.mpr
  constructor
  · intro a ha he
    obtain ⟨l,hl,ha⟩ := List.mem_flatten.mp ha
    obtain ⟨v,hv⟩ := List.mem_ofFn.mp hl
    subst l
    have hz := (coefficient_mem v 1 (tails v) a ha).2.1
    have hez := congrArg Index.z he
    simp [Index.origin] at hez
    omega
  · have hrows := rows_pairwise tails (List.finRange n) (List.nodup_finRange n)
    simpa [List.finRange,List.flatMap_def,List.map_ofFn,Function.comp_def] using hrows

theorem rawWords_valid (ops : RepresentedRing C R) {n : ℕ}
    (t J : ℕ) (ht : 0 < t) (hJ : 0 < J)
    (beta : C) (tails : Fin n → List C) (hlen : ∀ v, (tails v).length < J) :
    Sparse.ValidData Finset.univ t J (decodeRecords ops (rawWords beta tails)) := by
  intro a ha
  simp only [Sparse.keys,decodeRecords,List.map_map,Function.comp_def,
    rawWords,List.map_reverse,List.mem_reverse] at ha
  obtain ⟨b,hb,rfl⟩ := List.mem_map.mp ha
  rcases List.mem_cons.mp hb with he | hb
  · subst b
    simp [Index.Kept,Index.Valid,Index.origin,ht,hJ]
  · obtain ⟨l,hl,hb⟩ := List.mem_flatten.mp hb
    obtain ⟨v,hv⟩ := List.mem_ofFn.mp hl
    subst l
    obtain ⟨hu,hlo,hhi,hvars⟩ := coefficient_mem v 1 (tails v) b hb
    have hj : b.1.z < J := by have := hlen v; omega
    refine ⟨⟨by simpa [hu] using ht,hj⟩,?_,Finset.subset_univ _⟩
    simpa [Index.Valid,hvars] using hlo

def rawStored (ops : RepresentedRing C R) {n : ℕ}
    (t J : ℕ) (ht : 0 < t) (hJ : 0 < J)
    (beta : C) (tails : Fin n → List C) (hlen : ∀ v, (tails v).length < J) :
    Moments.Stored (R:=R) (Finset.univ : Finset (Fin n)) t J where
  data := decodeRecords ops (rawWords beta tails)
  valid := rawWords_valid ops t J ht hJ beta tails hlen
  nodup := by
    simpa [Sparse.keys,decodeRecords,List.map_map,Function.comp_def] using
      rawWords_nodup beta tails

private theorem decode_reverse {n : ℕ} (ops : RepresentedRing C R)
    (l : List (Index (Fin n) × C)) :
    Sparse.denote (decodeRecords ops l.reverse) = Sparse.denote (decodeRecords ops l) := by
  induction l with
  | nil => rfl
  | cons a l ih =>
      simp only [List.reverse_cons,decodeRecords,List.map_append,Sparse.denote,
        Sparse.decode_append,List.map_cons,List.map_nil,Sparse.decode,add_zero]
      change Sparse.denote (decodeRecords ops l.reverse) + _ =
        _ + Sparse.denote (decodeRecords ops l)
      rw [ih,add_comm]

private theorem decode_flatten {n : ℕ} (ops : RepresentedRing C R)
    (ls : List (List (Index (Fin n) × C))) :
    Sparse.denote (decodeRecords ops ls.flatten) =
      (ls.map fun l => Sparse.denote (decodeRecords ops l)).sum := by
  induction ls with
  | nil => rfl
  | cons l ls ih =>
      simp only [List.flatten_cons,decodeRecords,List.map_append,Sparse.denote,
        Sparse.decode_append,List.map_cons,List.sum_cons]
      exact congrArg (_ + ·) ih

theorem rawWords_denote (ops : RepresentedRing C R) {n : ℕ}
    (beta : C) (tails : Fin n → List C) :
    Sparse.denote (decodeRecords ops (rawWords beta tails)) =
      atom Index.origin (ops.decode beta) +
        ∑ v, Polynomial.C (Moments.variableZ v
          (Polynomial.X * polynomial ops (tails v))) := by
  rw [rawWords,decode_reverse]
  change atom Index.origin (ops.decode beta) +
    Sparse.denote (decodeRecords ops (List.ofFn fun v =>
      coefficientRecords v 1 (tails v)).flatten) = _
  rw [decode_flatten,List.map_ofFn,List.sum_ofFn]
  congr 1
  apply Finset.sum_congr rfl
  intro v _
  simpa only [Function.comp_apply,pow_one] using
    coefficientRecords_denote ops v 1 (tails v)

theorem tail_polynomial (ops : RepresentedRing C R) (cs : List C) :
    Polynomial.X * polynomial ops cs.tail = polynomial ops cs -
      Polynomial.C ((polynomial ops cs).coeff 0) := by
  cases cs with
  | nil => simp [polynomial,SubexponentialSAT.SubexpDensePolynomial.decodeList]
  | cons c cs =>
      simp [polynomial,SubexponentialSAT.SubexpDensePolynomial.decodeList,
        SubexponentialSAT.PolynomialAlgorithm.denote_cons]

/-- Removing the actual array's constant slot commutes with its Z truncation.
This concerns the shifted array, not truncation before shifting. -/
theorem tail_polynomial_eq_trunc_delta (ops : RepresentedRing C R)
    (J : ℕ) (cs : List C) (p : Polynomial R) (theta : R)
    (hp : polynomial ops cs = Truncation.trunc J
      (p.comp (Polynomial.X + Polynomial.C theta))) :
    Polynomial.X * polynomial ops cs.tail =
      Truncation.trunc J (Moments.rowDelta p theta) := by
  rw [tail_polynomial,hp]
  ext j
  by_cases hj : j=0
  · subst j
    simp
  · simp [Polynomial.coeff_C,hj,Moments.rowDelta]

theorem variableZ_trunc_C {n : ℕ} (t J : ℕ) (ht : 0 < t)
    (v : Fin n) (p : Polynomial R) :
    Polynomial.C (Moments.variableZ v (Truncation.trunc J p)) =
      canonical t J (Polynomial.C (Moments.variableZ v p)) := by
  ext u j
  by_cases hu : u=0 <;> by_cases hj : j < J <;>
    simp [Polynomial.coeff_C,hu,hj,ht,Moments.variableZ_coeff]

theorem rawWords_canonical_denote (ops : RepresentedRing C R) {n : ℕ}
    (t J : ℕ) (ht : 0 < t) (hJ : 0 < J)
    (beta : C) (tails : Fin n → List C) (row : Fin n → Polynomial R) (theta : R)
    (hrow : ∀ v, Polynomial.X * polynomial ops (tails v) =
      Truncation.trunc J (Moments.rowDelta (row v) theta)) :
    Sparse.denote (decodeRecords ops (rawWords beta tails)) =
      canonical t J (Moments.incidenceJet row theta (ops.decode beta)) := by
  rw [rawWords_denote]
  simp_rw [hrow,variableZ_trunc_C t J ht]
  have hc : atom Index.origin (ops.decode beta) =
      canonical t J (atom (Index.origin : Index (Fin n)) (ops.decode beta)) := by
    rw [canonical_atom]
    simp [Index.Kept,Index.origin,ht,hJ]
  rw [hc,←map_sum,←map_add]
  congr 1
  simp only [Moments.incidenceJet,Moments.incidenceZ,map_add,map_sum]
  rfl

end SubexponentialSAT.SqrtLog.PerturbationAssembly

end OAI.Algorithms

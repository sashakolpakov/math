import OAI.Analysis.DifferentialForms.Manifold.Bidegree
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Algebra.BigOperators.Group.Finset.Powerset
import Mathlib.LinearAlgebra.Determinant

/-! # Pure -/

namespace OAI.Analysis.HodgeTheory.Pure.Constructions.PolarizedPairing

noncomputable section

/-! PolarizedPairing: the maximal scalar character forces complex multilinearity.
The argument extends an identity of real polynomial evaluations to complex
evaluations and extracts the holomorphic projection.
-/

open scoped BigOperators
open Finset _root_.Polynomial

variable {E : Type*} [NormedAddCommGroup E]
  [NormedSpace ℝ E] [NormedSpace ℂ E] [IsScalarTower ℝ ℂ E]
  {n : ℕ}

def rotateSlots (s : Finset (Fin n)) (v : Fin n → E) : Fin n → E :=
  s.piecewise (fun i => Complex.I • v i) v

def rotationPolynomial (φ : E [⋀^Fin n]→L[ℝ] ℂ) (v : Fin n → E) : ℂ[X] :=
  ∑ s : Finset (Fin n), C (φ (rotateSlots s v)) * X ^ s.card

omit [IsScalarTower ℝ ℂ E] in
theorem rotationPolynomial_eval_real (φ : E [⋀^Fin n]→L[ℝ] ℂ)
    (v : Fin n → E) (t : ℝ) :
    (rotationPolynomial φ v).eval (t : ℂ) =
      φ (fun i => v i + t • (Complex.I • v i)) := by
  classical
  rw [rotationPolynomial]
  simp only [eval_finsetSum, eval_mul, eval_C, eval_pow, eval_X]
  rw [show (fun i => v i + t • (Complex.I • v i)) =
      (fun i => t • (Complex.I • v i)) + v by ext i; simp [add_comm]]
  change _ = φ.toMultilinearMap ((fun i => t • (Complex.I • v i)) + v)
  rw [φ.toMultilinearMap.map_add_univ]
  apply Finset.sum_congr rfl
  intro s _
  have h := φ.toMultilinearMap.map_piecewise_smul (fun _ => t) (rotateSlots s v) s
  simp only [prod_const, Complex.real_smul, Complex.ofReal_pow] at h
  have he : s.piecewise (fun i => t • rotateSlots s v i) (rotateSlots s v) =
      s.piecewise (fun i => t • (Complex.I • v i)) v := by
    ext i
    by_cases hi : i ∈ s <;> simp [rotateSlots, hi]
  rw [he] at h
  exact (mul_comm _ _).trans h.symm

theorem rotationPolynomial_pure (φ : E [⋀^Fin n]→L[ℝ] ℂ)
    (hφ : DifferentialForms.Manifold.Bidegree.HasBidegree E n 0 φ) (v : Fin n → E) :
    rotationPolynomial φ v = (1 + X * C Complex.I) ^ n * C (φ v) := by
  apply Polynomial.eq_of_infinite_eval_eq
  apply (Set.infinite_range_of_injective Complex.ofReal_injective).mono
  rintro _ ⟨t, rfl⟩
  change (rotationPolynomial φ v).eval (t : ℂ) = _
  rw [rotationPolynomial_eval_real]
  have hne : (1 : ℂ) + (t : ℂ) * Complex.I ≠ 0 := by
    intro he
    have hr := congrArg Complex.re he
    simp at hr
  have hp := hφ (Units.mk0 ((1 : ℂ) + (t : ℂ) * Complex.I) hne) v
  have hE (r : ℝ) (x : E) : (r : ℂ) • x = r • x := algebraMap_smul ℂ r x
  simp only [DifferentialForms.Manifold.Bidegree.bidegreeCharacter, Units.val_mk0, pow_zero, mul_one,
    add_smul, one_smul, mul_smul, hE] at hp
  simp only [eval_mul, eval_pow, eval_add, eval_one, eval_X, eval_C]
  convert hp using 1

theorem holomorphic_projection_sum (φ : E [⋀^Fin n]→L[ℝ] ℂ)
    (hφ : DifferentialForms.Manifold.Bidegree.HasBidegree E n 0 φ) (v : Fin n → E) :
    ∑ s : Finset (Fin n), (-Complex.I) ^ s.card * φ (rotateSlots s v) =
      (2 : ℂ) ^ n * φ v := by
  have h := congrArg (Polynomial.eval (-Complex.I)) (rotationPolynomial_pure φ hφ v)
  simp only [rotationPolynomial, eval_finsetSum, eval_mul, eval_C, eval_pow,
    eval_X, eval_add, eval_one, neg_mul, Complex.I_mul_I, neg_neg] at h
  rw [show (1 : ℂ) + 1 = 2 by norm_num] at h
  simpa only [mul_comm] using h

theorem sum_finsets_split (f : Finset (Fin n) → ℂ) (i : Fin n) :
    ∑ s, f s = ∑ s ∈ (Finset.univ.erase i).powerset, (f s + f (insert i s)) := by
  classical
  calc
    ∑ s, f s = ∑ s ∈ (Finset.univ : Finset (Fin n)).powerset, f s := by
      rw [Finset.powerset_univ]
    _ = _ := by
      conv_lhs => rw [← Finset.insert_erase (Finset.mem_univ i)]
      rw [Finset.sum_powerset_insert (Finset.notMem_erase i Finset.univ),
        Finset.sum_add_distrib]

omit [NormedSpace ℝ E] [IsScalarTower ℝ ℂ E] in
theorem rotateSlots_update (s : Finset (Fin n)) (i : Fin n) (hi : i ∉ s)
    (v : Fin n → E) :
    rotateSlots s (Function.update v i (Complex.I • v i)) =
      rotateSlots (insert i s) v := by
  classical
  ext j
  by_cases hj : j = i
  · subst j; simp [rotateSlots, hi]
  · by_cases hs : j ∈ s <;> simp [rotateSlots, hj, hs]

omit [NormedSpace ℝ E] [IsScalarTower ℝ ℂ E] in
theorem rotateSlots_insert_update (s : Finset (Fin n)) (i : Fin n) (_hi : i ∉ s)
    (v : Fin n → E) :
    rotateSlots (insert i s) (Function.update v i (Complex.I • v i)) =
      Function.update (rotateSlots s v) i (-v i) := by
  classical
  ext j
  by_cases hj : j = i
  · subst j; simp [rotateSlots, smul_smul]
  · by_cases hs : j ∈ s <;> simp [rotateSlots, hj, hs]

omit [IsScalarTower ℝ ℂ E] in
theorem projection_sum_update_I (φ : E [⋀^Fin n]→L[ℝ] ℂ)
    (v : Fin n → E) (i : Fin n) :
    (∑ s : Finset (Fin n), (-Complex.I) ^ s.card *
      φ (rotateSlots s (Function.update v i (Complex.I • v i)))) =
      Complex.I * ∑ s : Finset (Fin n), (-Complex.I) ^ s.card *
        φ (rotateSlots s v) := by
  classical
  rw [sum_finsets_split _ i, sum_finsets_split _ i, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro s hs
  have hi : i ∉ s := Finset.notMem_of_mem_powerset_of_notMem hs (Finset.notMem_erase i _)
  rw [rotateSlots_update s i hi, rotateSlots_insert_update s i hi,
    Finset.card_insert_of_notMem hi, pow_succ]
  have hneg : φ (Function.update (rotateSlots s v) i (-v i)) = -φ (rotateSlots s v) := by
    have he : Function.update (rotateSlots s v) i (v i) = rotateSlots s v := by
      apply Function.update_eq_self_iff.mpr
      simp [rotateSlots, hi]
    change φ.toMultilinearMap _ = -φ.toMultilinearMap _
    rw [φ.toMultilinearMap.map_update_neg, he]
  rw [hneg]
  ring_nf
  rw [Complex.I_sq]
  ring

theorem pure_update_I (φ : E [⋀^Fin n]→L[ℝ] ℂ)
    (hφ : DifferentialForms.Manifold.Bidegree.HasBidegree E n 0 φ) (v : Fin n → E) (i : Fin n) :
    φ (Function.update v i (Complex.I • v i)) = Complex.I * φ v := by
  have h := projection_sum_update_I φ v i
  rw [holomorphic_projection_sum φ hφ, holomorphic_projection_sum φ hφ] at h
  have htwo : (2 : ℂ) ^ n ≠ 0 := pow_ne_zero _ (by norm_num)
  apply mul_left_cancel₀ htwo
  simpa only [mul_left_comm] using h

theorem pure_update_complex_smul (φ : E [⋀^Fin n]→L[ℝ] ℂ)
    (hφ : DifferentialForms.Manifold.Bidegree.HasBidegree E n 0 φ) (v : Fin n → E) (i : Fin n) (z : ℂ) (x : E) :
    φ (Function.update v i (z • x)) = z * φ (Function.update v i x) := by
  classical
  have hE (r : ℝ) (y : E) : (r : ℂ) • y = r • y := algebraMap_smul ℂ r y
  have hz : z • x = z.re • x + z.im • (Complex.I • x) := by
    conv_lhs => rw [← Complex.re_add_im z, add_smul, mul_smul]
    rw [hE, hE]
  rw [hz]
  change φ.toMultilinearMap (Function.update v i _) = _
  rw [φ.toMultilinearMap.map_update_add,
    φ.toMultilinearMap.map_update_smul, φ.toMultilinearMap.map_update_smul]
  have hI := pure_update_I φ hφ (Function.update v i x) i
  simp only [Function.update_self, Function.update_idem] at hI
  change z.re • φ (Function.update v i x) +
    z.im • φ (Function.update v i (Complex.I • x)) = _
  rw [hI]
  simp only [Complex.real_smul]
  conv_rhs => rw [← Complex.re_add_im z]
  ring

/-- A pure `(n,0)` real alternating covector is complex multilinear. -/
def pureComplexAlternating (φ : E [⋀^Fin n]→L[ℝ] ℂ)
    (hφ : DifferentialForms.Manifold.Bidegree.HasBidegree E n 0 φ) : E [⋀^Fin n]→ₗ[ℂ] ℂ where
  toFun := φ
  map_update_add' v i x y := φ.map_update_add v i x y
  map_update_smul' := by
    intro d v i z x
    have hd : d = instDecidableEqFin n := Subsingleton.elim _ _
    subst d
    exact pure_update_complex_smul φ hφ v i z x
  map_eq_zero_of_eq' v i j hv hij := φ.map_eq_zero_of_eq v hv hij

@[simp]
theorem pureComplexAlternating_apply (φ : E [⋀^Fin n]→L[ℝ] ℂ)
    (hφ : DifferentialForms.Manifold.Bidegree.HasBidegree E n 0 φ) (v : Fin n → E) :
    pureComplexAlternating φ hφ v = φ v := rfl

theorem pure_eq_basis_det (φ : E [⋀^Fin n]→L[ℝ] ℂ)
    (hφ : DifferentialForms.Manifold.Bidegree.HasBidegree E n 0 φ) (b : Module.Basis (Fin n) ℂ E) (v : Fin n → E) :
    φ v = φ b * b.det v := by
  have h := congrArg (fun f : E [⋀^Fin n]→ₗ[ℂ] ℂ => f v)
    ((pureComplexAlternating φ hφ).eq_smul_basis_det b)
  exact h

theorem pure_basis_value_ne_zero (φ : E [⋀^Fin n]→L[ℝ] ℂ)
    (hφ : DifferentialForms.Manifold.Bidegree.HasBidegree E n 0 φ) (b : Module.Basis (Fin n) ℂ E) (hne : φ ≠ 0) :
    φ b ≠ 0 := by
  intro hz
  apply hne
  ext v
  rw [pure_eq_basis_det φ hφ b v, hz, zero_mul]
  rfl

end

end OAI.Analysis.HodgeTheory.Pure.Constructions.PolarizedPairing

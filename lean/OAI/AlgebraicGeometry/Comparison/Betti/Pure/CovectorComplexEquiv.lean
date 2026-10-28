import OAI.AlgebraicGeometry.Comparison.Betti.CovectorComplexProjection
import Mathlib.Analysis.Normed.Module.Alternating.Curry

/-! # Covector Complex Equiv -/

namespace OAI.AlgebraicGeometry.Comparison.Betti.Pure.CovectorComplexEquiv.Holomorphic

noncomputable section

section

/-! Contracting a pure holomorphic covector lowers its holomorphic degree by one. -/

open scoped BigOperators

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedSpace ℂ E]
  [IsScalarTower ℝ ℂ E] {n : ℕ}

def pureCovectorComplexMultilinearMap (ω : E [⋀^Fin n]→L[ℝ] ℂ) (hω : OAI.Analysis.DifferentialForms.Manifold.Bidegree.HasBidegree E n 0 ω) :
    MultilinearMap ℂ (fun _ : Fin n => E) ℂ :=
  CovectorComplexProjection.Holomorphic.homogeneousComplexMultilinearMap ω.toAlternatingMap.toMultilinearMap (fun z v => by
    change ω (fun i => (z : ℂ) • v i) = (z : ℂ) ^ n * ω v
    have h := hω z v
    change ω (fun i => (z : ℂ) • v i) = OAI.Analysis.DifferentialForms.Manifold.Bidegree.bidegreeCharacter n 0 z * ω v at h
    rw [OAI.Analysis.DifferentialForms.Manifold.Bidegree.bidegreeCharacter, pow_zero, mul_one] at h
    exact h)

theorem pureCovector_curryLeft (ω : E [⋀^Fin (n + 1)]→L[ℝ] ℂ)
    (hω : OAI.Analysis.DifferentialForms.Manifold.Bidegree.HasBidegree E (n + 1) 0 ω) (x : E) : OAI.Analysis.DifferentialForms.Manifold.Bidegree.HasBidegree E n 0 (ω.curryLeft x) := by
  let P := pureCovectorComplexMultilinearMap ω hω
  intro z v
  change Fin n → E at v
  change ω (Fin.cons x (fun i => (z : ℂ) • v i)) = OAI.Analysis.DifferentialForms.Manifold.Bidegree.bidegreeCharacter n 0 z * ω (Fin.cons x v)
  rw [show OAI.Analysis.DifferentialForms.Manifold.Bidegree.bidegreeCharacter n 0 z = (z : ℂ) ^ n by simp [OAI.Analysis.DifferentialForms.Manifold.Bidegree.bidegreeCharacter]]
  have hv : Fin.cons x (fun i => (z : ℂ) • v i) =
      fun i : Fin (n + 1) => ((Fin.cons (1 : ℂ) (fun _ : Fin n => (z : ℂ)) : Fin (n + 1) → ℂ) i) •
        (Fin.cons x v : Fin (n + 1) → E) i := by
    funext i
    refine Fin.cases ?_ (fun j => ?_) i
    · simp
    · rfl
  rw [hv]
  change P (fun i => ((Fin.cons (1 : ℂ) (fun _ : Fin n => (z : ℂ)) : Fin (n + 1) → ℂ) i) •
      (Fin.cons x v : Fin (n + 1) → E) i) =
    (z : ℂ) ^ n * P (Fin.cons x v)
  rw [P.map_smul_univ]
  simp only [Fin.prod_univ_succ, Fin.cons_zero, Fin.cons_succ, Finset.prod_const,
    Finset.card_univ, Fintype.card_fin, one_mul, smul_eq_mul]

end

/-! Pure holomorphic real covectors are exactly actual complex alternating covectors. -/

open scoped BigOperators

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedSpace ℂ E]
  [IsScalarTower ℝ ℂ E] {n : ℕ}

def pureCovectorComplexAlternatingMap (ω : E [⋀^Fin n]→L[ℝ] ℂ)
    (hω : OAI.Analysis.DifferentialForms.Manifold.Bidegree.HasBidegree E n 0 ω) : E [⋀^Fin n]→L[ℂ] ℂ where
  toMultilinearMap := pureCovectorComplexMultilinearMap ω hω
  cont := ω.cont
  map_eq_zero_of_eq' v _ _ hij hne := ω.map_eq_zero_of_eq v hij hne

theorem complexCovector_restrictScalars_pure (ω : E [⋀^Fin n]→L[ℂ] ℂ) :
    OAI.Analysis.DifferentialForms.Manifold.Bidegree.HasBidegree E n 0 (ω.restrictScalars ℝ) := by
  intro z v
  change Fin n → E at v
  change ω (fun i => (z : ℂ) • v i) = OAI.Analysis.DifferentialForms.Manifold.Bidegree.bidegreeCharacter n 0 z * ω v
  have h := ω.toMultilinearMap.map_smul_univ (fun _ : Fin n => (z : ℂ)) v
  change ω (fun i => (z : ℂ) • v i) = (∏ _i : Fin n, (z : ℂ)) • ω v at h
  simpa only [Finset.prod_const, Finset.card_univ, Fintype.card_fin, OAI.Analysis.DifferentialForms.Manifold.Bidegree.bidegreeCharacter,
    pow_zero, mul_one, smul_eq_mul] using h

def pureCovectorComplexEquiv (E : Type) [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedSpace ℂ E] [IsScalarTower ℝ ℂ E] (n : ℕ) :
    OAI.Analysis.DifferentialForms.Manifold.Bidegree.pureBidegreeSubmodule E n 0 ≃ₗ[ℂ] (E [⋀^Fin n]→L[ℂ] ℂ) where
  toFun ω := pureCovectorComplexAlternatingMap ω.val ω.property
  invFun ω := ⟨ω.restrictScalars ℝ, complexCovector_restrictScalars_pure ω⟩
  left_inv ω := by
    apply Subtype.ext
    ext v
    rfl
  right_inv ω := by
    ext v
    rfl
  map_add' ω η := by
    ext v
    rfl
  map_smul' c ω := by
    ext v
    rfl

theorem pureCovectorComplexEquiv_apply (ω : OAI.Analysis.DifferentialForms.Manifold.Bidegree.pureBidegreeSubmodule E n 0) (v : Fin n → E) :
    pureCovectorComplexEquiv E n ω v = ω.val v := rfl

end

end OAI.AlgebraicGeometry.Comparison.Betti.Pure.CovectorComplexEquiv.Holomorphic

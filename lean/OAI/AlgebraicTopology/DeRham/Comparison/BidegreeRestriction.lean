import OAI.Analysis.DifferentialForms.Manifold.Bidegree
import OAI.AlgebraicTopology.DeRham.Comparison.ComplexTangent

/-! # Bidegree Restriction -/

namespace OAI.AlgebraicTopology.DeRham.Comparison.BidegreeRestriction

noncomputable section

/-!
# Pure covectors and complex-linear tangent pullback

The bidegree condition here is the actual complex-scalar eigencharacter of
real continuous alternating covectors from `Forms.Bidegree`. It is preserved
under complex-linear maps of tangent spaces and is unchanged by a complex
linear change of coordinates. No cohomological comparison is assumed.
-/

variable {V W : Type*}
  [NormedAddCommGroup V] [NormedSpace ℝ V] [NormedSpace ℂ V]
  [IsScalarTower ℝ ℂ V]
  [NormedAddCommGroup W] [NormedSpace ℝ W] [NormedSpace ℂ W]
  [IsScalarTower ℝ ℂ W]

/-- Restricting a pure covector along a complex-linear tangent map preserves
its two complex degrees. -/
theorem hasBidegree_pullback {p q : ℕ}
    {ω : W [⋀^Fin (p + q)]→L[ℝ] ℂ} (hω : Analysis.DifferentialForms.Manifold.Bidegree.HasBidegree W p q ω)
    (j : V →L[ℂ] W) :
    Analysis.DifferentialForms.Manifold.Bidegree.HasBidegree V p q (ω.compContinuousLinearMap (j.restrictScalars ℝ)) := by
  intro z v
  change ω (fun i => j ((z : ℂ) • v i)) =
    Analysis.DifferentialForms.Manifold.Bidegree.bidegreeCharacter p q z * ω (fun i => j (v i))
  simpa only [map_smul] using hω z (fun i => j (v i))

/-- Pure covectors therefore have a genuine complex-linear pullback map. -/
def pureBidegreePullback (p q : ℕ) (j : V →L[ℂ] W) :
    Analysis.DifferentialForms.Manifold.Bidegree.pureBidegreeSubmodule W p q →ₗ[ℂ] Analysis.DifferentialForms.Manifold.Bidegree.pureBidegreeSubmodule V p q where
  toFun ω := ⟨(ω : W [⋀^Fin (p + q)]→L[ℝ] ℂ).compContinuousLinearMap
    (j.restrictScalars ℝ), hasBidegree_pullback ω.property j⟩
  map_add' ω η := by
    apply Subtype.ext
    ext v
    rfl
  map_smul' c ω := by
    apply Subtype.ext
    ext v
    rfl

@[simp]
theorem pureBidegreePullback_apply (p q : ℕ) (j : V →L[ℂ] W)
    (ω : Analysis.DifferentialForms.Manifold.Bidegree.pureBidegreeSubmodule W p q) (v : Fin (p + q) → V) :
    (pureBidegreePullback p q j ω : V [⋀^Fin (p + q)]→L[ℝ] ℂ) v =
      (ω : W [⋀^Fin (p + q)]→L[ℝ] ℂ) (fun i => j (v i)) := rfl

/-- Purity is intrinsic under a complex-linear change of tangent coordinates. -/
theorem hasBidegree_pullback_equiv_iff {p q : ℕ}
    (ω : W [⋀^Fin (p + q)]→L[ℝ] ℂ) (e : V ≃L[ℂ] W) :
    Analysis.DifferentialForms.Manifold.Bidegree.HasBidegree V p q
      (ω.compContinuousLinearMap (e.toContinuousLinearMap.restrictScalars ℝ)) ↔
        Analysis.DifferentialForms.Manifold.Bidegree.HasBidegree W p q ω := by
  constructor
  · intro h z v
    have hv := h z (fun i => e.symm (v i))
    change ω (fun i => e ((z : ℂ) • e.symm (v i))) =
      Analysis.DifferentialForms.Manifold.Bidegree.bidegreeCharacter p q z * ω (fun i => e (e.symm (v i))) at hv
    simpa only [map_smul, ContinuousLinearEquiv.apply_symm_apply] using hv
  · intro h
    exact hasBidegree_pullback h e.toContinuousLinearMap

end

end OAI.AlgebraicTopology.DeRham.Comparison.BidegreeRestriction

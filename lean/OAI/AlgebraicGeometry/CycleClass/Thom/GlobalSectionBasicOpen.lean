import OAI.AlgebraicGeometry.CycleClass.Thom.Scheme.SectionEvaluation

/-! # Global Section Basic Open -/

namespace OAI.AlgebraicGeometry.CycleClass.Thom.GlobalSectionBasicOpen.Constructions

noncomputable section

/-! The actual basic open of a global regular section is exactly the
nonvanishing locus of its native complex-point evaluation. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

theorem underlying_mem_basicOpen_iff (X : Over Foundations.Scheme.ProjectiveSpace.complexBase) (s : Γ(X.left, ⊤)) (x : ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X) :
    ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.underlying x ∈ X.left.basicOpen s ↔ DivisorClass.Chern.AnalyticTransitions.Construction.globalSectionEvaluation x s ≠ 0 := by
  change ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.basePoint ∈ x.left ⁻¹ᵁ X.left.basicOpen s ↔ _
  rw [Scheme.preimage_basicOpen_top]
  change ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.basePoint ∈
    (Spec (CommRingCat.of ℂ)).basicOpen (x.left.appTop s) ↔ _
  rw [basicOpen_eq_of_affine', PrimeSpectrum.mem_basicOpen]
  change ((Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom (x.left.appTop s)) ∉ (⊥ : Ideal ℂ) ↔ _
  rw [Ideal.mem_bot]
  rfl

theorem analyticBasicOpen_eq (X : Over Foundations.Scheme.ProjectiveSpace.complexBase) (s : Γ(X.left, ⊤)) :
    (Thom.Scheme.SectionEvaluation.Constructions.analyticOpen X (X.left.basicOpen s) : Set (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X)) =
      {x | DivisorClass.Chern.AnalyticTransitions.Construction.globalSectionEvaluation x s ≠ 0} := by
  ext x
  exact underlying_mem_basicOpen_iff X s x

end

end OAI.AlgebraicGeometry.CycleClass.Thom.GlobalSectionBasicOpen.Constructions

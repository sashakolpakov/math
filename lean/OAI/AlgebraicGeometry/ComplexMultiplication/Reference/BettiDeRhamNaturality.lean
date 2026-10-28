import OAI.AlgebraicGeometry.ComplexMultiplication.Reference.SingularConstantCohomologyNaturality
import OAI.AlgebraicGeometry.ComplexMultiplication.Reference.CoefficientNaturality
import OAI.AlgebraicGeometry.ComplexMultiplication.GroupPullback
import OAI.AlgebraicGeometry.ComplexMultiplication.AbelianGroups

/-! # Betti De Rham Naturality -/

namespace OAI.AlgebraicGeometry.ComplexMultiplication.Reference.BettiDeRhamNaturality

noncomputable section

open scoped OAI.AlgebraicGeometry.Hodge.Filtration.ComplexPoint

/-! # The original Betti-to-de Rham comparison intertwines actual algebraic pullback

This compares the unchanged original constant-sheaf cohomology and its genuine
holomorphic de Rham inclusion with actual singular and algebraic scheme maps.
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry ComplexPoint OAI.AlgebraicTopology.Singular

section

variable {X Y : Over (Spec (.of ℂ))} (R : Type) [Field R] [Algebra R ℂ]
  [IsIntegral X.left] [Smooth X.hom] [IsIntegral Y.left] [Smooth Y.hom]

/-- The original field-to-de Rham map commutes with actual constant hypercohomology pullback. -/
theorem originalDeRhamHypercohomologyPullback_fieldComparison (f : X ⟶ Y) (n : ℕ)
    (β : ComplexPoint.Basic.ComplexSchemePoint.Hypercohomology Y (ComplexPoint.Basic.ComplexSchemePoint.constantFieldSheafComplexInt R Y) (n : ℤ)) :
    FilteredPullback.originalDeRhamHypercohomologyPullback f (n : ℤ)
        (ComplexPoint.Basic.ComplexSchemePoint.hypercohomologyMap Y (ComplexPoint.Basic.ComplexSchemePoint.fieldToHolomorphicDeRhamComplexInt R Y) (n : ℤ) β) =
      ComplexPoint.Basic.ComplexSchemePoint.hypercohomologyMap X (ComplexPoint.Basic.ComplexSchemePoint.fieldToHolomorphicDeRhamComplexInt R X) (n : ℤ)
        (SingularConstantNaturality.originalCoefficientConstantHypercohomologyPullback R f (n : ℤ) β) := by
  let γ := HypercohomologyPullback.originalHypercohomologyPullback f (ComplexPoint.Basic.ComplexSchemePoint.constantFieldSheafComplexInt R Y) (n : ℤ) β
  have hn := HypercohomologyPullback.originalHypercohomologyPullback_naturality f
    (ComplexPoint.Basic.ComplexSchemePoint.fieldToHolomorphicDeRhamComplexInt R Y) (n : ℤ) β
  have hc := CoefficientNaturality.originalDeRhamInverseImagePullback_fieldComparison R f
  exact (congrArg (ComplexPoint.Basic.ComplexSchemePoint.hypercohomologyMap X (InverseImageMap.originalDeRhamInverseImagePullback f) (n : ℤ)) hn).trans
    ((ComplexPoint.Basic.ComplexSchemePoint.hypercohomologyMap_comp_apply X
      ((AnalyticInverseImage.originalAnalyticInverseImageLocalizer f).functor.map
        (ComplexPoint.Basic.ComplexSchemePoint.fieldToHolomorphicDeRhamComplexInt R Y))
      (InverseImageMap.originalDeRhamInverseImagePullback f) (n : ℤ) γ).symm.trans
        ((congrArg (fun g ↦ ComplexPoint.Basic.ComplexSchemePoint.hypercohomologyMap X g (n : ℤ) γ) hc).trans
          (ComplexPoint.Basic.ComplexSchemePoint.hypercohomologyMap_comp_apply X
            (ConstantDeRhamNaturality.originalCoefficientComplexInverseImageIso f (AddCommGrpCat.of R)).hom
            (ComplexPoint.Basic.ComplexSchemePoint.fieldToHolomorphicDeRhamComplexInt R X) (n : ℤ) γ)))

variable [Foundations.ProjectiveSpaceIs.IsProjective X.hom] [Foundations.ProjectiveSpaceIs.IsProjective Y.hom]

/-- The unchanged singular/constant and coefficient/de Rham comparisons intertwine scheme maps. -/
theorem originalBettiDeRhamComparison_naturality (f : X ⟶ Y) (n : ℕ)
    (α : AlgebraicTopology.Singular.CohomologyTo.Cohomology R (TopCat.of (ComplexPoint.Basic.ComplexSchemePoint Y)) n) :
    FilteredPullback.originalDeRhamHypercohomologyPullback f (n : ℤ)
        (ComplexPoint.Basic.ComplexSchemePoint.fieldToDeRhamCohomologyLinear R Y n
          (CanonicalSheafComparison.canonicalSingularToConstantSheafLinearEquiv R Y n α)) =
      ComplexPoint.Basic.ComplexSchemePoint.fieldToDeRhamCohomologyLinear R X n
        (CanonicalSheafComparison.canonicalSingularToConstantSheafLinearEquiv R X n
          (AlgebraicTopology.Singular.CohomologyTo.cohomologyMap R n (DeRhamPresheafPullback.originalAnalyticSchemeMap f) α)) := by
  let β := (ComplexPoint.Basic.ComplexSchemePoint.hypercohomologyAddEquivConstantCohomology R Y n).symm
    (CanonicalSheafComparison.canonicalSingularToConstantSheafLinearEquiv R Y n α)
  exact (originalDeRhamHypercohomologyPullback_fieldComparison R f n β).trans
    (congrArg (ComplexPoint.Basic.ComplexSchemePoint.hypercohomologyMap X (ComplexPoint.Basic.ComplexSchemePoint.fieldToHolomorphicDeRhamComplexInt R X) (n : ℤ))
      (SingularConstantCohomologyNaturality.originalSingularToConstantHypercohomology_naturality R f n α))

end

variable (X : Over (Spec (.of ℂ))) [IsIntegral X.left] [Smooth X.hom]
  [Foundations.ProjectiveSpaceIs.IsProjective X.hom] [GrpObj X]

/-- The actual original rational H¹ action is intertwined with actual original de Rham pullback. -/
theorem groupEndomorphismH1Pullback_deRham (f : GroupEndomorphismRing.GroupEndomorphism X) (v : H^1(X; ℚ)) :
    FilteredPullback.originalDeRhamHypercohomologyPullback (GroupEndomorphismRing.GroupEndomorphism.toHom X f) 1
        (ComplexPoint.Basic.ComplexSchemePoint.fieldToDeRhamCohomologyLinear ℚ X 1 v) =
      ComplexPoint.Basic.ComplexSchemePoint.fieldToDeRhamCohomologyLinear ℚ X 1 (GroupPullback.groupEndomorphismH1Pullback X f v) := by
  obtain ⟨α, rfl⟩ := (CanonicalSheafComparison.canonicalSingularToConstantSheafLinearEquiv ℚ X 1).surjective v
  simpa only [GroupPullback.groupEndomorphismH1Pullback, LinearEquiv.conjAlgEquiv_apply,
    LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply] using!
      originalBettiDeRhamComparison_naturality ℚ (GroupEndomorphismRing.GroupEndomorphism.toHom X f) 1 α

end

end OAI.AlgebraicGeometry.ComplexMultiplication.Reference.BettiDeRhamNaturality

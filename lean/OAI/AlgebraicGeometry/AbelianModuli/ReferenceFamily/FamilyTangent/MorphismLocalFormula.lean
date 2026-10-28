import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.FamilyMorphism.DefectCoboundary
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.FamilyMorphism.PulledTangentDifference

/-! # Morphism Local Formula -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.FamilyTangent.MorphismLocalFormula

noncomputable section

/-! On compatible original affine opens, the source tangent cocycle
composed with the native conormal pullback differs from the pulled target
tangent cocycle by the difference of the actual local morphism defects. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj TensorProduct

variable (R : Type) [CommRing R] [Algebra ℂ R] [Algebra R ℂ] [IsScalarTower ℂ R ℂ]
    {X Y : Over (Spec (.of R))} [Smooth X.hom] [Smooth Y.hom]
    [IsIntegral (TangentBasePoint.fixedFamilyFiber ℂ R X).left] [Smooth (TangentBasePoint.fixedFamilyFiber ℂ R X).hom]
    [GrpObj (TangentBasePoint.fixedFamilyFiber ℂ R X)]
    [IsIntegral (TangentBasePoint.fixedFamilyFiber ℂ R Y).left] [Smooth (TangentBasePoint.fixedFamilyFiber ℂ R Y).hom]
    [GrpObj (TangentBasePoint.fixedFamilyFiber ℂ R Y)]
    (f : X ⟶ Y)
    [IsMonHom (show TangentBasePoint.fixedFamilyFiber ℂ R X ⟶ TangentBasePoint.fixedFamilyFiber ℂ R Y from
      (Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap R ℂ)))).map f)]

theorem familyTangentMorphism_localFormula
    (V U₀ U₁ : X.left.affineOpens) (W Z₀ Z₁ : Y.left.affineOpens)
    (h : V.1 ≤ f.left ⁻¹ᵁ W.1) (t₀ : V.1 ≤ U₀.1) (t₁ : V.1 ≤ U₁.1)
    (j₀ : W.1 ≤ Z₀.1) (j₁ : W.1 ≤ Z₁.1) (d : Derivation ℂ R ℂ)
    (z : Constructed.IdentityConormal.constructedIdentityConormal ℂ (TangentBasePoint.fixedFamilyFiber ℂ R Y)) :
    FixedFiber.AffineCoefficient.fixedFiberConormalLinearEquiv R X V (Family.CommonOpenTangentDifferences.familyCommonOpenTangentDifference ℂ R X t₀ t₁ d)
        (Intrinsic.GroupConormalMap.constructedConormalPullback (show TangentBasePoint.fixedFamilyFiber ℂ R X ⟶ TangentBasePoint.fixedFamilyFiber ℂ R Y from
          (Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap R ℂ)))).map f) z) -
      FamilyMorphism.TensorCoordinates.familyMorphismTensorCoordinates R ℂ f V W h
        (FixedFiber.AffineCoefficient.fixedFiberConormalLinearEquiv R Y W (Family.CommonOpenTangentDifferences.familyCommonOpenTangentDifference ℂ R Y j₀ j₁ d) z) =
    FamilyMorphism.GroupRetractions.familyMorphismConormalDefect R f V U₁ W Z₁ h t₁ j₁ d z -
      FamilyMorphism.GroupRetractions.familyMorphismConormalDefect R f V U₀ W Z₀ h t₀ j₀ d z := by
  have H := congrArg (fun w => w z) (FamilyMorphism.DefectCoboundary.familyMorphismDefect_coboundary R f V U₀ U₁ W Z₀ Z₁ h t₀ t₁ j₀ j₁ d)
  simp only [LinearMap.sub_apply, LinearMap.comp_apply] at H
  rw [FamilyMorphism.PulledTangentDifference.familyMorphismPulledConormalDifference_tangent] at H
  exact H

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.FamilyTangent.MorphismLocalFormula

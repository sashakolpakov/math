import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.FamilyTangent.MorphismLocalFormula
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.FamilyMorphism.RegularDefects
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.FamilyMorphism.RegularSections
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Family.CommonOpenRegularDifference

/-! # Morphism Regular Formula -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.FamilyTangent.MorphismRegularFormula

noncomputable section

/-! The local formula for the original tangent cocycles is an
equality of original regular sections: source minus pulled target is
the difference of the actual regular morphism defects. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj

attribute [local implicit_reducible] TangentBasePoint.fixedFamilyFiber

variable (R : Type) [CommRing R] [Algebra ℂ R] [Algebra R ℂ] [IsScalarTower ℂ R ℂ]
    {X Y : Over (Spec (.of R))} [Smooth X.hom] [Smooth Y.hom]
    [IsIntegral (TangentBasePoint.fixedFamilyFiber ℂ R X).left] [Smooth (TangentBasePoint.fixedFamilyFiber ℂ R X).hom]
    [GrpObj (TangentBasePoint.fixedFamilyFiber ℂ R X)]
    [IsIntegral (TangentBasePoint.fixedFamilyFiber ℂ R Y).left] [Smooth (TangentBasePoint.fixedFamilyFiber ℂ R Y).hom]
    [GrpObj (TangentBasePoint.fixedFamilyFiber ℂ R Y)]
    (f : X ⟶ Y)
    [IsMonHom (show TangentBasePoint.fixedFamilyFiber ℂ R X ⟶ TangentBasePoint.fixedFamilyFiber ℂ R Y from
      (Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap R ℂ)))).map f)]

theorem familyTangentMorphism_regularFormula
    (V U₀ U₁ : X.left.affineOpens) (W Z₀ Z₁ : Y.left.affineOpens)
    (h : V.1 ≤ f.left ⁻¹ᵁ W.1) (t₀ : V.1 ≤ U₀.1) (t₁ : V.1 ≤ U₁.1)
    (j₀ : W.1 ≤ Z₀.1) (j₁ : W.1 ≤ Z₁.1) (d : Derivation ℂ R ℂ)
    (z : Constructed.IdentityConormal.constructedIdentityConormal ℂ (TangentBasePoint.fixedFamilyFiber ℂ R Y)) :
    Family.CommonOpenRegularDifference.familyCommonOpenRegularDifference R X t₀ t₁ d
        (Intrinsic.GroupConormalMap.constructedConormalPullback (show TangentBasePoint.fixedFamilyFiber ℂ R X ⟶ TangentBasePoint.fixedFamilyFiber ℂ R Y from
          (Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap R ℂ)))).map f) z) -
      (show Γ((TangentBasePoint.fixedFamilyFiber ℂ R X).left, FixedFiber.CoordinateProjection.fixedFiberAffineOpen R ℂ X V) from
        ((Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap R ℂ)))).map f).left.appLE
        (FixedFiber.CoordinateProjection.fixedFiberAffineOpen R ℂ Y W) (FixedFiber.CoordinateProjection.fixedFiberAffineOpen R ℂ X V) (FamilyMorphism.RegularSections.familyMorphismFixedFiber_open_le R ℂ f V W h)
        (Family.CommonOpenRegularDifference.familyCommonOpenRegularDifference R Y j₀ j₁ d z)) =
    FamilyMorphism.RegularDefects.familyMorphismRegularDefect R f V U₁ W Z₁ h t₁ j₁ d z -
      FamilyMorphism.RegularDefects.familyMorphismRegularDefect R f V U₀ W Z₀ h t₀ j₀ d z := by
  have H := congrArg (FixedFiber.RegularSections.fixedFiberRegularSectionEquiv R ℂ X V)
    (MorphismLocalFormula.familyTangentMorphism_localFormula R f V U₀ U₁ W Z₀ Z₁ h t₀ t₁ j₀ j₁ d z)
  rw [map_sub, map_sub, FamilyMorphism.RegularSections.fixedFiberRegularSectionEquiv_morphism] at H
  exact H

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.FamilyTangent.MorphismRegularFormula

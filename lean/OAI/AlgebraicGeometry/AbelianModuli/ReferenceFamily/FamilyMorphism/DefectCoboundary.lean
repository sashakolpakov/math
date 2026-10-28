import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.FamilyMorphism.GroupRetractions
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.FixedFiber.AffineCoefficient
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.ConormalLiftMorphismDefect

/-! # Defect Coboundary -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.FamilyMorphism.DefectCoboundary

noncomputable section

/-! For an original family morphism inducing a group morphism on the
fixed fiber, the actual local retraction defects give the coboundary
relating the source tangent difference and the pulled target difference. -/

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

attribute [local irreducible] Family.CommonOpenGroupRetractions.familyCommonOpenGroupRetraction GroupRetractions.familyMorphismGroupRetraction

theorem familyMorphismDefect_coboundary
    (V U₀ U₁ : X.left.affineOpens) (W Z₀ Z₁ : Y.left.affineOpens)
    (h : V.1 ≤ f.left ⁻¹ᵁ W.1) (t₀ : V.1 ≤ U₀.1) (t₁ : V.1 ≤ U₁.1)
    (j₀ : W.1 ≤ Z₀.1) (j₁ : W.1 ≤ Z₁.1) (d : Derivation ℂ R ℂ) :
    (FixedFiber.AffineCoefficient.fixedFiberConormalLinearEquiv R X V (Family.CommonOpenTangentDifferences.familyCommonOpenTangentDifference ℂ R X t₀ t₁ d)).comp
        (Intrinsic.GroupConormalMap.constructedConormalPullback (show TangentBasePoint.fixedFamilyFiber ℂ R X ⟶ TangentBasePoint.fixedFamilyFiber ℂ R Y from
          (Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap R ℂ)))).map f)) -
      GroupRetractions.familyMorphismPulledConormalDifference R f V W Z₀ h j₀ d Z₁ j₁ =
    GroupRetractions.familyMorphismConormalDefect R f V U₁ W Z₁ h t₁ j₁ d -
      GroupRetractions.familyMorphismConormalDefect R f V U₀ W Z₀ h t₀ j₀ d := by
  let C := ℂ ⊗[R] Family.AffineTangentLifts.familyAffineRing R X V
  have : Algebra.FiniteType ℂ C := FixedFiber.AffineCoefficient.fixedFiberAffineRing_finiteType R X V
  have : _root_.IsReduced C := FixedFiber.AffineCoefficient.fixedFiberAffineRing_reduced R X V
  let F : TangentBasePoint.fixedFamilyFiber ℂ R X ⟶ TangentBasePoint.fixedFamilyFiber ℂ R Y :=
    (Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap R ℂ)))).map f
  let a₀ := Family.CommonOpenGroupRetractions.familyCommonOpenGroupRetraction R X t₁ d
  let a₁ := Family.CommonOpenGroupRetractions.familyCommonOpenGroupRetraction R X t₀ d
  let b₀ := GroupRetractions.familyMorphismGroupRetraction R f V W Z₁ h j₁ d
  let b₁ := GroupRetractions.familyMorphismGroupRetraction R f V W Z₀ h j₀ d
  have H := ConormalLiftMorphismDefect.conormalLiftMorphismDefect_coboundary F C a₀.val a₁.val b₀.val b₁.val
    (a₁.property.trans a₀.property.symm) (b₁.property.trans b₀.property.symm)
    (GroupRetractions.familyMorphismRetraction_reduction R f V U₁ W Z₁ h t₁ j₁ d)
    (GroupRetractions.familyMorphismRetraction_reduction R f V U₀ W Z₀ h t₀ j₀ d)
  have hc := Family.CommonOpenGroupRetractions.familyCommonOpenGroupRetraction_conormal R X t₀ t₁ d
  exact (congrArg (fun v => v.comp (Intrinsic.GroupConormalMap.constructedConormalPullback F) -
    GroupRetractions.familyMorphismPulledConormalDifference R f V W Z₀ h j₀ d Z₁ j₁) hc.symm).trans H

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.FamilyMorphism.DefectCoboundary

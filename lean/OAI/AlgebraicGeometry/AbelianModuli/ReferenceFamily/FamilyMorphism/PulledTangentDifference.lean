import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.FamilyMorphism.GroupRetractions
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.FixedFiber.AffineCoefficient
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Affine.ConormalDeformedSquare

/-! # Pulled Tangent Difference -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.FamilyMorphism.PulledTangentDifference

noncomputable section

/-! The conormal difference of the actual pulled target retractions
is the original target tangent difference pulled by the literal
fixed-fiber coefficient map. This includes empty affine source opens. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj TensorProduct

attribute [local implicit_reducible] EtaleSplittingAt.EtaleSplitting.affineOver FixedFiber.AffineDiagram.fixedFiberTensorDiagram FixedFiber.AffineDiagram.fixedFiberTensorAlgebras
attribute [local implicit_reducible] Affine.OpenDiagram.familyAffineCoordinateFunctor HilbertConstruction.Affine.CoordinateFunctor.affineCoordinateFunctor HilbertConstruction.AlgebraTensorFunctor.algebraTensorFunctor
attribute [local irreducible] Family.CommonOpenGroupRetractions.familyCommonOpenGroupRetraction GroupRetractions.familyMorphismGroupRetraction
attribute [local irreducible] ProductCoordinates.familyMorphismProductCoordinates

variable (R : Type) [CommRing R] [Algebra ℂ R] [Algebra R ℂ] [IsScalarTower ℂ R ℂ]
    {X Y : Over (Spec (.of R))} [Smooth X.hom] [Smooth Y.hom]
    [IsIntegral (TangentBasePoint.fixedFamilyFiber ℂ R X).left] [Smooth (TangentBasePoint.fixedFamilyFiber ℂ R X).hom]
    [IsIntegral (TangentBasePoint.fixedFamilyFiber ℂ R Y).left] [Smooth (TangentBasePoint.fixedFamilyFiber ℂ R Y).hom]
    [GrpObj (TangentBasePoint.fixedFamilyFiber ℂ R Y)]
    (f : X ⟶ Y) (V : X.left.affineOpens) (W Z Z' : Y.left.affineOpens)
    (h : V.1 ≤ f.left ⁻¹ᵁ W.1) (j : W.1 ≤ Z.1) (j' : W.1 ≤ Z'.1) (d : Derivation ℂ R ℂ)

theorem familyMorphismPulledConormalDifference_tangent
    (z : Constructed.IdentityConormal.constructedIdentityConormal ℂ (TangentBasePoint.fixedFamilyFiber ℂ R Y)) :
    GroupRetractions.familyMorphismPulledConormalDifference R f V W Z h j d Z' j' z =
      TensorCoordinates.familyMorphismTensorCoordinates R ℂ f V W h
        (FixedFiber.AffineCoefficient.fixedFiberConormalLinearEquiv R Y W (Family.CommonOpenTangentDifferences.familyCommonOpenTangentDifference ℂ R Y j j' d) z) := by
  let B := CommAlgCat.of ℂ (ℂ ⊗[R] Family.AffineTangentLifts.familyAffineRing R Y W)
  let C := CommAlgCat.of ℂ (ℂ ⊗[R] Family.AffineTangentLifts.familyAffineRing R X V)
  let i : EtaleSplittingAt.EtaleSplitting.affineOver ℂ B ⟶ TangentBasePoint.fixedFamilyFiber ℂ R Y := FixedFiber.AffineDiagram.fixedFiberTensorInclusion R ℂ Y W
  have : IsOpenImmersion i.left := FixedFiber.AffineDiagram.fixedFiberTensorInclusion_open R ℂ Y W
  let q : B →ₐ[ℂ] C := TensorCoordinates.familyMorphismTensorCoordinates R ℂ f V W h
  cases subsingleton_or_nontrivial C with
  | inl hC =>
    let := hC
    exact Subsingleton.elim _ _
  | inr hC =>
    let := hC
    have : Nontrivial B := q.toRingHom.domain_nontrivial
    have : IsDomain B := Affine.PresentationConormalLinearity.affinePresentationAlgebra_isDomain (TangentBasePoint.fixedFamilyFiber ℂ R Y) B i
    have : Algebra.Smooth ℂ B := FixedFiber.AffineCoefficient.fixedFiberAffineRing_smooth R Y W
    have : Algebra.FiniteType ℂ C := FixedFiber.AffineCoefficient.fixedFiberAffineRing_finiteType R X V
    have : _root_.IsReduced C := FixedFiber.AffineCoefficient.fixedFiberAffineRing_reduced R X V
    let : Algebra B C := q.toRingHom.toAlgebra
    have : IsScalarTower ℂ B C := IsScalarTower.of_algHom q
    let m := ProductCoordinates.familyMorphismProductCoordinates ℂ R f V W h d
    let a := Family.CommonOpenGroupRetractions.familyCommonOpenGroupRetraction R Y j' d
    let b := Family.CommonOpenGroupRetractions.familyCommonOpenGroupRetraction R Y j d
    let a' := GroupRetractions.familyMorphismGroupRetraction R f V W Z' h j' d
    let b' := GroupRetractions.familyMorphismGroupRetraction R f V W Z h j d
    have H := Affine.ConormalDeformedSquare.affineConormalDeformedPullback_originalSquare (TangentBasePoint.fixedFamilyFiber ℂ R Y) B i C
      (Dual.TensorMapCoordinates.dualTensorMapCoordinates m)
      (Dual.TensorMapCoordinates.dualTensorMapCoordinates_reduction m q (ProductCoordinates.familyMorphismProductCoordinates_reduction ℂ R f V W h d))
      (Dual.TensorMapCoordinates.dualTensorMapCoordinates_eps m) a b a'.val b'.val (b'.property.trans a'.property.symm)
      (GroupRetractions.familyMorphismGroupRetraction_value R f V W Z' h j' d).symm
      (GroupRetractions.familyMorphismGroupRetraction_value R f V W Z h j d).symm z
    have hc := congrArg (fun w => w z) (Family.CommonOpenGroupRetractions.familyCommonOpenGroupRetraction_conormal R Y j j' d)
    exact H.trans (congrArg q hc)

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.FamilyMorphism.PulledTangentDifference

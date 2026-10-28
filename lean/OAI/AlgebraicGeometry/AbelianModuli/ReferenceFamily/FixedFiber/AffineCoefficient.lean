import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Affine.PresentationConormalLinearity
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.FixedFiber.AffineDiagram
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.FixedFiber.DerivationPresheaf
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.TangentBasePoint
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Affine.ChartConormalRestriction

/-! # Affine Coefficient -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.FixedFiber.AffineCoefficient

noncomputable section

section

/-! Derivations in the original fixed-fiber tensor coordinates have
native identity-conormal coordinates. The comparison is complex-linear
and commutes with the actual open restriction maps. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj
open scoped TensorProduct

attribute [local irreducible] Affine.PresentationConormalLinearity.affinePresentationConormalLinearEquiv
attribute [local implicit_reducible] AffineDiagram.fixedFiberTensorDiagram AffineDiagram.fixedFiberTensorAlgebras
attribute [local implicit_reducible] Affine.OpenDiagram.familyAffineCoordinateFunctor HilbertConstruction.Affine.CoordinateFunctor.affineCoordinateFunctor HilbertConstruction.AlgebraTensorFunctor.algebraTensorFunctor

variable (R : Type) [CommRing R] [Algebra R ℂ] (X : Over (Spec (.of R)))
    [IsIntegral (TangentBasePoint.fixedFamilyFiber ℂ R X).left] [Smooth (TangentBasePoint.fixedFamilyFiber ℂ R X).hom]
    [GrpObj (TangentBasePoint.fixedFamilyFiber ℂ R X)]

def fixedFiberConormalLinearEquiv (V : X.left.affineOpens) :
    Derivation ℂ (ℂ ⊗[R] Family.AffineTangentLifts.familyAffineRing R X V)
        (ℂ ⊗[R] Family.AffineTangentLifts.familyAffineRing R X V) ≃ₗ[ℂ]
      (Constructed.IdentityConormal.constructedIdentityConormal ℂ (TangentBasePoint.fixedFamilyFiber ℂ R X) →ₗ[ℂ]
        ℂ ⊗[R] Family.AffineTangentLifts.familyAffineRing R X V) := by
  let B := CommAlgCat.of ℂ (ℂ ⊗[R] Family.AffineTangentLifts.familyAffineRing R X V)
  let i : EtaleSplittingAt.EtaleSplitting.affineOver ℂ B ⟶ TangentBasePoint.fixedFamilyFiber ℂ R X := AffineDiagram.fixedFiberTensorInclusion R ℂ X V
  have : IsOpenImmersion i.left := AffineDiagram.fixedFiberTensorInclusion_open R ℂ X V
  exact (Affine.PresentationConormalLinearity.affinePresentationConormalLinearEquiv (TangentBasePoint.fixedFamilyFiber ℂ R X) B i).restrictScalars ℂ

theorem fixedFiberConormalLinearEquiv_natural {V W : X.left.affineOpens} (h : V.1 ≤ W.1)
    (d : Derivation ℂ (ℂ ⊗[R] Family.AffineTangentLifts.familyAffineRing R X W) (ℂ ⊗[R] Family.AffineTangentLifts.familyAffineRing R X W))
    (z : Constructed.IdentityConormal.constructedIdentityConormal ℂ (TangentBasePoint.fixedFamilyFiber ℂ R X)) :
    fixedFiberConormalLinearEquiv R X V (DerivationPresheaf.fixedFiberDerivationRestriction R ℂ X h d) z =
      DerivationPresheaf.fixedFiberTensorRestriction R ℂ X h (fixedFiberConormalLinearEquiv R X W d z) := by
  let BV := CommAlgCat.of ℂ (ℂ ⊗[R] Family.AffineTangentLifts.familyAffineRing R X V)
  let BW := CommAlgCat.of ℂ (ℂ ⊗[R] Family.AffineTangentLifts.familyAffineRing R X W)
  let iV : EtaleSplittingAt.EtaleSplitting.affineOver ℂ BV ⟶ TangentBasePoint.fixedFamilyFiber ℂ R X := AffineDiagram.fixedFiberTensorInclusion R ℂ X V
  let iW : EtaleSplittingAt.EtaleSplitting.affineOver ℂ BW ⟶ TangentBasePoint.fixedFamilyFiber ℂ R X := AffineDiagram.fixedFiberTensorInclusion R ℂ X W
  have hiV : IsOpenImmersion iV.left := AffineDiagram.fixedFiberTensorInclusion_open R ℂ X V
  have hiW : IsOpenImmersion iW.left := AffineDiagram.fixedFiberTensorInclusion_open R ℂ X W
  exact Affine.PresentationConormalLinearity.affinePresentationConormalLinearEquiv_natural (TangentBasePoint.fixedFamilyFiber ℂ R X) BW iW BV iV
    (DerivationPresheaf.fixedFiberTensorRestriction R ℂ X h) (DerivationPresheaf.fixedFiberTensorRestriction_etale R ℂ X h)
    (AffineDiagram.fixedFiberTensorInclusion_natural R ℂ X (homOfLE h)) d z

end

/-! Original tensor rings of affine opens in the smooth integral
fixed fiber are smooth, finite type, and reduced, including empty opens. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped TensorProduct

attribute [local implicit_reducible] EtaleSplittingAt.EtaleSplitting.affineOver AffineDiagram.fixedFiberTensorDiagram AffineDiagram.fixedFiberTensorAlgebras
attribute [local implicit_reducible] Affine.OpenDiagram.familyAffineCoordinateFunctor HilbertConstruction.Affine.CoordinateFunctor.affineCoordinateFunctor HilbertConstruction.AlgebraTensorFunctor.algebraTensorFunctor

variable (R : Type) [CommRing R] [Algebra R ℂ] (X : Over (Spec (.of R)))
    [Smooth (TangentBasePoint.fixedFamilyFiber ℂ R X).hom] (V : X.left.affineOpens)

theorem fixedFiberAffineRing_smooth : Algebra.Smooth ℂ (ℂ ⊗[R] Family.AffineTangentLifts.familyAffineRing R X V) := by
  let B := CommAlgCat.of ℂ (ℂ ⊗[R] Family.AffineTangentLifts.familyAffineRing R X V)
  let i : EtaleSplittingAt.EtaleSplitting.affineOver ℂ B ⟶ TangentBasePoint.fixedFamilyFiber ℂ R X := AffineDiagram.fixedFiberTensorInclusion R ℂ X V
  have : IsOpenImmersion i.left := AffineDiagram.fixedFiberTensorInclusion_open R ℂ X V
  exact Affine.PresentationConormalLinearity.affinePresentationAlgebra_smooth (TangentBasePoint.fixedFamilyFiber ℂ R X) B i

theorem fixedFiberAffineRing_finiteType : Algebra.FiniteType ℂ (ℂ ⊗[R] Family.AffineTangentLifts.familyAffineRing R X V) := by
  have : Algebra.Smooth ℂ (ℂ ⊗[R] Family.AffineTangentLifts.familyAffineRing R X V) := fixedFiberAffineRing_smooth R X V
  infer_instance

omit [Smooth (TangentBasePoint.fixedFamilyFiber ℂ R X).hom] in
theorem fixedFiberAffineRing_reduced [IsIntegral (TangentBasePoint.fixedFamilyFiber ℂ R X).left] :
    _root_.IsReduced (ℂ ⊗[R] Family.AffineTangentLifts.familyAffineRing R X V) := by
  let B := CommAlgCat.of ℂ (ℂ ⊗[R] Family.AffineTangentLifts.familyAffineRing R X V)
  let i : EtaleSplittingAt.EtaleSplitting.affineOver ℂ B ⟶ TangentBasePoint.fixedFamilyFiber ℂ R X := AffineDiagram.fixedFiberTensorInclusion R ℂ X V
  have : IsOpenImmersion i.left := AffineDiagram.fixedFiberTensorInclusion_open R ℂ X V
  cases subsingleton_or_nontrivial B with
  | inl h =>
    let := h
    exact inferInstanceAs (_root_.IsReduced B)
  | inr h =>
    let := h
    have : IsDomain B := Affine.PresentationConormalLinearity.affinePresentationAlgebra_isDomain (TangentBasePoint.fixedFamilyFiber ℂ R X) B i
    exact inferInstanceAs (_root_.IsReduced B)

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.FixedFiber.AffineCoefficient

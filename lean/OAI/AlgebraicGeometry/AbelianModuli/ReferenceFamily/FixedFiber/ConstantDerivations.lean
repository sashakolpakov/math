import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.FixedFiber.AffineCoefficient
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.ConormalUnitLogCoordinates

/-! # Constant Derivations -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.FixedFiber.ConstantDerivations

noncomputable section

/-! Constant native conormal covectors determine actual derivations
on every fixed-fiber affine open. The original coefficient-linear
comparison shows that these derivations and unit logarithms restrict
by the original tensor maps. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj TensorProduct

attribute [local irreducible] Affine.PresentationConormalLinearity.affinePresentationConormalLinearEquiv
attribute [local implicit_reducible] AffineDiagram.fixedFiberTensorDiagram AffineDiagram.fixedFiberTensorAlgebras
attribute [local implicit_reducible] Affine.OpenDiagram.familyAffineCoordinateFunctor HilbertConstruction.Affine.CoordinateFunctor.affineCoordinateFunctor HilbertConstruction.AlgebraTensorFunctor.algebraTensorFunctor

variable (R : Type) [CommRing R] [Algebra R ℂ] (X : Over (Spec (.of R)))
    [IsIntegral (TangentBasePoint.fixedFamilyFiber ℂ R X).left] [Smooth (TangentBasePoint.fixedFamilyFiber ℂ R X).hom]
    [GrpObj (TangentBasePoint.fixedFamilyFiber ℂ R X)]

def fixedFiberConormalCoefficientEquiv (V : X.left.affineOpens) :
    Derivation ℂ (ℂ ⊗[R] Family.AffineTangentLifts.familyAffineRing R X V) (ℂ ⊗[R] Family.AffineTangentLifts.familyAffineRing R X V) ≃ₗ[ℂ ⊗[R] Family.AffineTangentLifts.familyAffineRing R X V]
      (Constructed.IdentityConormal.constructedIdentityConormal ℂ (TangentBasePoint.fixedFamilyFiber ℂ R X) →ₗ[ℂ] (ℂ ⊗[R] Family.AffineTangentLifts.familyAffineRing R X V)) := by
  let B := CommAlgCat.of ℂ (ℂ ⊗[R] Family.AffineTangentLifts.familyAffineRing R X V)
  let i : EtaleSplittingAt.EtaleSplitting.affineOver ℂ B ⟶ TangentBasePoint.fixedFamilyFiber ℂ R X := AffineDiagram.fixedFiberTensorInclusion R ℂ X V
  have : IsOpenImmersion i.left := AffineDiagram.fixedFiberTensorInclusion_open R ℂ X V
  exact Affine.PresentationConormalLinearity.affinePresentationConormalLinearEquiv (TangentBasePoint.fixedFamilyFiber ℂ R X) B i

theorem fixedFiberConormalCoefficientEquiv_restrictScalars (V : X.left.affineOpens) :
    (fixedFiberConormalCoefficientEquiv R X V).restrictScalars ℂ = AffineCoefficient.fixedFiberConormalLinearEquiv R X V := rfl

def fixedFiberConstantConormalDerivation (V : X.left.affineOpens)
    (l : Constructed.IdentityConormal.constructedIdentityConormal ℂ (TangentBasePoint.fixedFamilyFiber ℂ R X) →ₗ[ℂ] ℂ) :
    Derivation ℂ (ℂ ⊗[R] Family.AffineTangentLifts.familyAffineRing R X V) (ℂ ⊗[R] Family.AffineTangentLifts.familyAffineRing R X V) :=
  (fixedFiberConormalCoefficientEquiv R X V).symm (ConormalUnitLogCoordinates.coefficientCovector (ℂ ⊗[R] Family.AffineTangentLifts.familyAffineRing R X V) l)

theorem fixedFiberConstantConormalDerivation_coordinates (V : X.left.affineOpens)
    (l : Constructed.IdentityConormal.constructedIdentityConormal ℂ (TangentBasePoint.fixedFamilyFiber ℂ R X) →ₗ[ℂ] ℂ) :
    AffineCoefficient.fixedFiberConormalLinearEquiv R X V (fixedFiberConstantConormalDerivation R X V l) =
      ConormalUnitLogCoordinates.coefficientCovector (ℂ ⊗[R] Family.AffineTangentLifts.familyAffineRing R X V) l :=
  (fixedFiberConormalCoefficientEquiv R X V).apply_symm_apply _

theorem fixedFiberConstantConormalDerivation_restrict {V W : X.left.affineOpens} (h : V.1 ≤ W.1)
    (l : Constructed.IdentityConormal.constructedIdentityConormal ℂ (TangentBasePoint.fixedFamilyFiber ℂ R X) →ₗ[ℂ] ℂ) :
    DerivationPresheaf.fixedFiberDerivationRestriction R ℂ X h (fixedFiberConstantConormalDerivation R X W l) =
      fixedFiberConstantConormalDerivation R X V l := by
  apply (AffineCoefficient.fixedFiberConormalLinearEquiv R X V).injective
  apply LinearMap.ext
  intro z
  rw [AffineCoefficient.fixedFiberConormalLinearEquiv_natural, fixedFiberConstantConormalDerivation_coordinates,
    fixedFiberConstantConormalDerivation_coordinates]
  exact (DerivationPresheaf.fixedFiberTensorRestriction R ℂ X h).commutes (l z)

theorem fixedFiberConstantConormalUnitLog_restrict {V W : X.left.affineOpens} (h : V.1 ≤ W.1)
    (l : Constructed.IdentityConormal.constructedIdentityConormal ℂ (TangentBasePoint.fixedFamilyFiber ℂ R X) →ₗ[ℂ] ℂ)
    (u : (ℂ ⊗[R] Family.AffineTangentLifts.familyAffineRing R X W)ˣ) :
    CoefficientUnitLogarithms.coefficientUnitLog (fixedFiberConstantConormalDerivation R X V l)
        (Units.map (DerivationPresheaf.fixedFiberTensorRestriction R ℂ X h).toMonoidHom u) =
      DerivationPresheaf.fixedFiberTensorRestriction R ℂ X h (CoefficientUnitLogarithms.coefficientUnitLog (fixedFiberConstantConormalDerivation R X W l) u) := by
  have he (a : ℂ ⊗[R] Family.AffineTangentLifts.familyAffineRing R X W) :
      fixedFiberConstantConormalDerivation R X V l (DerivationPresheaf.fixedFiberTensorRestriction R ℂ X h a) =
        DerivationPresheaf.fixedFiberTensorRestriction R ℂ X h (fixedFiberConstantConormalDerivation R X W l a) := by
    rw [← fixedFiberConstantConormalDerivation_restrict R X h l]
    exact EtaleHomDerivation.etaleAlgHomDerivationLinear_map (DerivationPresheaf.fixedFiberTensorRestriction R ℂ X h)
      (DerivationPresheaf.fixedFiberTensorRestriction_etale R ℂ X h) (fixedFiberConstantConormalDerivation R X W l) a
  exact CoefficientUnitLogarithms.coefficientUnitLog_map (DerivationPresheaf.fixedFiberTensorRestriction R ℂ X h) (DerivationPresheaf.fixedFiberTensorRestriction R ℂ X h)
    (fun _ => rfl) _ _ he u

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.FixedFiber.ConstantDerivations

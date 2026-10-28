import OAI.NumberTheory.PadicHodge.IntegralComparison.Intrinsic.CoefficientPurity
import OAI.NumberTheory.PadicHodge.IntegralComparison.Affine.CoefficientRestriction
import OAI.NumberTheory.PadicHodge.IntegralComparison.Affine.HomSectionsEquiv
import OAI.NumberTheory.PadicHodge.IntegralComparison.SurjectiveScalarHom

/-! # Intrinsic Coefficient Hom -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Affine.IntrinsicCoefficientHom

noncomputable section

/-! Native finite-projective coefficient purity takes values in the
actual internal Hom into the globally identified scalar dualizing sheaf,
without any scalar-purity frame.
Its normalization is literal evaluation on coefficient sections. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u
open OAI.NumberTheory.PadicHodge.IntegralComparison.AffineOpen.InternalHom OAI.NumberTheory.PadicHodge.IntegralComparison.Resolution.CohomologyMaps OAI.NumberTheory.PadicHodge.IntegralComparison.Quotient.CoefficientEvaluation

variable {X : Scheme.{u}} (U : X.Opens) (hU : IsAffineOpen U)
  (N : X.Modules) [N.IsQuasicoherent]
  (K L : ChainComplex X.Modules ℕ)
  [∀ q, (K.X q).IsQuasicoherent] [∀ q, (L.X q).IsQuasicoherent]
  [∀ q, ((LinearResolutionPurity.internalComplex N K).X q).IsQuasicoherent]
  [∀ q, ((LinearResolutionPurity.internalComplex N L).X q).IsQuasicoherent]
  (M M' : X.Modules) [M.IsQuasicoherent] [M'.IsQuasicoherent]
  (ε : K ⟶ (ChainComplex.single₀ X.Modules).obj M) [QuasiIso ε]
  (ε' : L ⟶ (ChainComplex.single₀ X.Modules).obj M') [QuasiIso ε']
  [∀ q, Projective ((AffineOpen.InternalHom.sections U hU).obj (K.X q))]
  [∀ q, Projective ((AffineOpen.InternalHom.sections U hU).obj (L.X q))]
  (Q : Type u) [CommRing Q] [Algebra Γ(X, U) Q]
  (hQ : Function.Surjective (algebraMap Γ(X, U) Q))
  (C : Type u) [AddCommGroup C] [Module Q C] [Module Γ(X, U) C]
  [IsScalarTower Γ(X, U) Q C] [Module.Finite Q C] [Module.Projective Q C]
  (eM : (AffineOpen.InternalHom.sections U hU).obj M ≅ ModuleCat.of Γ(X, U) Q)
  (eC : (AffineOpen.InternalHom.sections U hU).obj M' ≅ ModuleCat.of Γ(X, U) C)
  (n : ℕ)
  (V : X.Modules) [Module Q Γ(V, U)] [IsScalarTower Γ(X, U) Q Γ(V, U)]
  (κ : (LinearResolutionPurity.internalComplex N K).homology n ≅ V)

def scalarIso : Quotient.CoefficientEvaluation.group Γ(X, U) ((AffineOpen.InternalHom.sections U hU).obj N) n
    (CoefficientLifts.resolution U hU K M ε (ModuleCat.of Γ(X, U) Q) eM) ≅
      ModuleCat.of Γ(X, U) Γ(V, U) :=
  (AffinePrincipal.Cohomology.Comparison.comparison U hU N K n).symm ≪≫
    (ModuleExactSections.sections U).mapIso κ

def coefficientIso : Γ(M', U) ≃ₗ[Γ(X, U)] C :=
  ((ChartSections.iso U hU M') ≪≫ eC).toLinearEquiv

def linearEquiv : Γ((LinearResolutionPurity.internalComplex N L).homology n, U) ≃ₗ[Γ(X, U)]
    (Γ(M', U) →ₗ[Γ(X, U)] Γ(V, U)) :=
  ((AffinePrincipal.Cohomology.Comparison.comparison U hU N L n).toLinearEquiv.trans
    (Intrinsic.CoefficientPurity.equiv Γ(X, U) Q hQ ((AffineOpen.InternalHom.sections U hU).obj N) n
      (CoefficientLifts.resolution U hU K M ε (ModuleCat.of Γ(X, U) Q) eM)
      Γ(V, U) (scalarIso U hU N K M ε Q eM n V κ) C
      (CoefficientLifts.resolution U hU L M' ε' (ModuleCat.of Γ(X, U) C) eC))).trans
    ((SurjectiveScalarHom.equiv Γ(X, U) Q hQ C Γ(V, U)).trans
      (LinearEquiv.arrowCongr (coefficientIso U hU M' C eC).symm (LinearEquiv.refl Γ(X, U) Γ(V, U))))

def iso : (ModuleExactSections.sections U).obj
    ((LinearResolutionPurity.internalComplex N L).homology n) ≅
      (ModuleExactSections.sections U).obj (ArithmeticGeometry.OrdinaryLocus.Openness.SheafHomModule.Construction.sheafHomModule M' V) :=
  ((linearEquiv U hU N K L M M' ε ε' Q hQ C eM eC n V κ).trans
    (HomSectionsEquiv.equiv U hU M' V).symm).toModuleIso

omit [N.IsQuasicoherent] in
theorem evaluation
    (z : Γ((LinearResolutionPurity.internalComplex N L).homology n, U))
    (m : Γ(M', U)) :
    ArithmeticGeometry.OrdinaryLocus.Openness.SheafHomEvaluation.Construction.sheafHomEvalAtOpen M' V U
        ((iso U hU N K L M M' ε ε' Q hQ C eM eC n V κ).hom z) m =
      κ.hom.app U (CoefficientRestriction.pullback U hU N K L M M' ε ε' Q C eM eC n z
        (coefficientIso U hU M' C eC m)) := by
  change HomSectionsEquiv.equiv U hU M' V
      ((HomSectionsEquiv.equiv U hU M' V).symm
        (linearEquiv U hU N K L M M' ε ε' Q hQ C eM eC n V κ z)) m = _
  rw [LinearEquiv.apply_symm_apply]
  change Intrinsic.CoefficientPurity.equiv Γ(X, U) Q hQ ((AffineOpen.InternalHom.sections U hU).obj N) n
    (CoefficientLifts.resolution U hU K M ε (ModuleCat.of Γ(X, U) Q) eM)
    Γ(V, U) (scalarIso U hU N K M ε Q eM n V κ) C
    (CoefficientLifts.resolution U hU L M' ε' (ModuleCat.of Γ(X, U) C) eC)
    ((AffinePrincipal.Cohomology.Comparison.comparison U hU N L n).hom z)
    (coefficientIso U hU M' C eC m) = _
  rw [Intrinsic.CoefficientPurity.equiv_apply]
  rfl

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Affine.IntrinsicCoefficientHom

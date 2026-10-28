import OAI.NumberTheory.PadicHodge.IntegralComparison.Affine.HomCohomologyNaturality
import OAI.NumberTheory.PadicHodge.IntegralComparison.Affine.CoefficientLifts
import OAI.NumberTheory.PadicHodge.IntegralComparison.ProjectiveCoefficient.Purity

/-! # Coefficient Evaluation -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Affine.CoefficientEvaluation

noncomputable section

/-! Finite projective coefficient evaluation on the actual sections of
native dual cohomology sheaves. Original augmented chain maps induce the
literal coefficient pullback in this normalized identification. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry Opposite

set_option backward.isDefEq.respectTransparency false

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
  (eM' : (AffineOpen.InternalHom.sections U hU).obj M' ≅ ModuleCat.of Γ(X, U) C)

abbrev scalarResolution := CoefficientLifts.resolution U hU K M ε (ModuleCat.of Γ(X, U) Q) eM
abbrev coefficientResolution := CoefficientLifts.resolution U hU L M' ε'
  (ModuleCat.of Γ(X, U) C) eM'

variable (n : ℕ)
  (e : Quotient.CoefficientEvaluation.group Γ(X, U) ((AffineOpen.InternalHom.sections U hU).obj N) n (scalarResolution U hU K M ε Q eM) ≅
    ModuleCat.of Γ(X, U) Q)
  (V : Type u) [AddCommGroup V] [Module Q V] [Module Γ(X, U) V] [IsScalarTower Γ(X, U) Q V]
  (eV : Quotient.CoefficientEvaluation.group Γ(X, U) ((AffineOpen.InternalHom.sections U hU).obj N) n (scalarResolution U hU K M ε Q eM) ≅
    ModuleCat.of Γ(X, U) V)

def equiv :
    ((ModuleExactSections.sections U).obj
      ((LinearResolutionPurity.internalComplex N L).homology n)) ≃ₗ[Γ(X, U)] (C →ₗ[Q] V) :=
  (AffinePrincipal.Cohomology.Comparison.comparison U hU N L n).toLinearEquiv.trans
    (ProjectiveCoefficient.Purity.equiv Γ(X, U) Q hQ ((AffineOpen.InternalHom.sections U hU).obj N) n
      (scalarResolution U hU K M ε Q eM) e C (coefficientResolution U hU L M' ε' C eM') V eV)

def scalarIso :
    (ModuleExactSections.sections U).obj
      ((LinearResolutionPurity.internalComplex N K).homology n) ≅ ModuleCat.of Γ(X, U) V :=
  AffinePrincipal.Cohomology.Comparison.comparison U hU N K n ≪≫ eV

variable (f : M ⟶ M') (a : K ⟶ L)
  (ha : a ≫ ε' = ε ≫ (ChainComplex.single₀ X.Modules).map f)
  (v : Q →ₗ[Q] C)
  (hv : (AffineOpen.InternalHom.sections U hU).map f ≫ eM'.hom = eM.hom ≫ ModuleCat.ofHom (v.restrictScalars Γ(X, U)))

include ha hv in
omit [N.IsQuasicoherent] in
theorem coefficient_map
    (z : Γ((LinearResolutionPurity.internalComplex N L).homology n, U)) :
    (scalarIso U hU N K M ε Q eM n V eV).hom
      ((ModuleExactSections.sections U).map
        (HomologicalComplex.homologyMap (HomCohomologyNaturality.nativeMap N K L a) n) z) =
    equiv U hU N K L M M' ε ε' Q hQ C eM eM' n e V eV z (v 1) := by
  have hn := HomCohomologyNaturality.naturality U hU N K L a n
  have hx := ConcreteCategory.congr_hom hn z
  have hl := CoefficientLifts.augmentation U hU K M ε (ModuleCat.of Γ(X, U) Q) eM
    L M' ε' (ModuleCat.of Γ(X, U) C) eM' f a ha
    (ModuleCat.ofHom (v.restrictScalars Γ(X, U))) hv
  have hm := Resolution.CohomologyMaps.map_eq
    (Resolution.CohomologyMaps.homFunctor Γ(X, U) ((AffineOpen.InternalHom.sections U hU).obj N))
    (scalarResolution U hU K M ε Q eM) (coefficientResolution U hU L M' ε' C eM')
    (ModuleCat.ofHom (v.restrictScalars Γ(X, U)))
    (HomCohomologyNaturality.chartMap U hU K L a) hl n
  have he := ProjectiveCoefficient.Purity.coefficient_map Γ(X, U) Q hQ
    ((AffineOpen.InternalHom.sections U hU).obj N) n (scalarResolution U hU K M ε Q eM) e C
    (coefficientResolution U hU L M' ε' C eM') V eV v
    ((AffinePrincipal.Cohomology.Comparison.comparison U hU N L n).hom z)
  rw [hm] at he
  exact (congrArg (fun x => eV.hom x) hx).trans he

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Affine.CoefficientEvaluation

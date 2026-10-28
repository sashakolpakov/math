import OAI.NumberTheory.PadicHodge.IntegralComparison.Affine.IntrinsicCoefficientHom
import OAI.NumberTheory.PadicHodge.IntegralComparison.ProjectiveRefinement.AffineMap
import OAI.NumberTheory.PadicHodge.IntegralComparison.Intrinsic.CoefficientPurity
import OAI.NumberTheory.PadicHodge.IntegralComparison.Affine.CoefficientRestriction
import OAI.NumberTheory.PadicHodge.IntegralComparison.Affine.HomSectionsEquiv
import OAI.NumberTheory.PadicHodge.IntegralComparison.SurjectiveScalarHom

/-! # Coefficient Point Evaluation -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Affine.CoefficientPointEvaluation

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

variable (d : (LinearResolutionPurity.internalComplex N L).homology n ⟶
    (LinearResolutionPurity.internalComplex N K).homology n)
  (z : Γ((LinearResolutionPurity.internalComplex N L).homology n, U))
  (m : Γ(M', U)) (v : C)
  (hm : IntrinsicCoefficientHom.coefficientIso U hU M' C eC m = v)
  (hd : (AffinePrincipal.Cohomology.Comparison.comparison U hU N K n).hom (d.app U z) =
    Resolution.CohomologyMaps.map (Resolution.CohomologyMaps.homFunctor Γ(X, U) ((AffineOpen.InternalHom.sections U hU).obj N))
      (CoefficientLifts.resolution U hU K M ε (ModuleCat.of Γ(X, U) Q) eM)
      (CoefficientLifts.resolution U hU L M' ε' (ModuleCat.of Γ(X, U) C) eC)
      (Quotient.CoefficientEvaluation.point Γ(X, U) Q C v) n
      ((AffinePrincipal.Cohomology.Comparison.comparison U hU N L n).hom z))

include hm hd in
omit [N.IsQuasicoherent] in
theorem evaluation :
    ArithmeticGeometry.OrdinaryLocus.Openness.SheafHomEvaluation.Construction.sheafHomEvalAtOpen M' V U
      ((IntrinsicCoefficientHom.iso U hU N K L M M' ε ε' Q hQ C eM eC n V κ).hom z) m =
      κ.hom.app U (d.app U z) := by
  have he := IntrinsicCoefficientHom.evaluation U hU N K L M M' ε ε' Q hQ C eM eC n V κ z m
  rw [hm] at he
  have hp : CoefficientRestriction.pullback U hU N K L M M' ε ε' Q C eM eC n z v = d.app U z := by
    apply (ConcreteCategory.bijective_of_isIso
      (AffinePrincipal.Cohomology.Comparison.comparison U hU N K n).hom).injective
    rw [CoefficientRestriction.comparison_pullback]
    exact hd.symm
  exact he.trans (congrArg (κ.hom.app U) hp)

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Affine.CoefficientPointEvaluation

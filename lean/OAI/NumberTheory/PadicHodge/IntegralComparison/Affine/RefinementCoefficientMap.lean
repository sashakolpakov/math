import OAI.NumberTheory.PadicHodge.IntegralComparison.Affine.CoefficientRestriction

/-! # Refinement Coefficient Map -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Affine.RefinementCoefficientMap

noncomputable section

/-! Actual coefficient maps formed through a common augmented
resolution induce the canonical coefficient pullback on affine Ext.
The identity side is cancelled using genuine resolution homotopy
invariance. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u
open OAI.NumberTheory.PadicHodge.IntegralComparison.AffineOpen.InternalHom OAI.NumberTheory.PadicHodge.IntegralComparison.Resolution.CohomologyMaps OAI.NumberTheory.PadicHodge.IntegralComparison.Quotient.CoefficientEvaluation

def identityIso {R : Type u} [CommRing R] (T D : ModuleCat.{u} R)
    (P Q : ProjectiveResolution D) (n : ℕ) :
    Resolution.CohomologyMaps.cohomology (Resolution.CohomologyMaps.homFunctor R T) Q n ≅ Resolution.CohomologyMaps.cohomology (Resolution.CohomologyMaps.homFunctor R T) P n where
  hom := Resolution.CohomologyMaps.map (Resolution.CohomologyMaps.homFunctor R T) P Q (𝟙 D) n
  inv := Resolution.CohomologyMaps.map (Resolution.CohomologyMaps.homFunctor R T) Q P (𝟙 D) n
  hom_inv_id := by rw [← Resolution.CohomologyMaps.map_comp, Category.id_comp, Resolution.CohomologyMaps.map_id]
  inv_hom_id := by rw [← Resolution.CohomologyMaps.map_comp, Category.id_comp, Resolution.CohomologyMaps.map_id]

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
  (D D' : ModuleCat Γ(X, U))
  (eM : (AffineOpen.InternalHom.sections U hU).obj M ≅ D) (eM' : (AffineOpen.InternalHom.sections U hU).obj M' ≅ D')
  (f : M ⟶ M') (a : K ⟶ L)
  (ha : a ≫ ε' = ε ≫ (ChainComplex.single₀ X.Modules).map f)
  (v : D ⟶ D') (hv : (AffineOpen.InternalHom.sections U hU).map f ≫ eM'.hom = eM.hom ≫ v)

include ha hv in
omit [N.IsQuasicoherent] in
theorem comparison_map (n : ℕ)
    (z : Γ((LinearResolutionPurity.internalComplex N L).homology n, U)) :
    (AffinePrincipal.Cohomology.Comparison.comparison U hU N K n).hom
      ((ModuleExactSections.sections U).map
        (HomologicalComplex.homologyMap (HomCohomologyNaturality.nativeMap N K L a) n) z) =
    Resolution.CohomologyMaps.map (Resolution.CohomologyMaps.homFunctor Γ(X, U) ((AffineOpen.InternalHom.sections U hU).obj N))
      (CoefficientLifts.resolution U hU K M ε D eM)
      (CoefficientLifts.resolution U hU L M' ε' D' eM') v n
      ((AffinePrincipal.Cohomology.Comparison.comparison U hU N L n).hom z) := by
  have hl := CoefficientLifts.augmentation U hU K M ε D eM L M' ε' D' eM' f a ha v hv
  have hm := Resolution.CohomologyMaps.map_eq
    (Resolution.CohomologyMaps.homFunctor Γ(X, U) ((AffineOpen.InternalHom.sections U hU).obj N))
    (CoefficientLifts.resolution U hU K M ε D eM)
    (CoefficientLifts.resolution U hU L M' ε' D' eM') v
    (HomCohomologyNaturality.chartMap U hU K L a) hl n
  rw [hm]
  exact ConcreteCategory.congr_hom (HomCohomologyNaturality.naturality U hU N K L a n) z

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Affine.RefinementCoefficientMap

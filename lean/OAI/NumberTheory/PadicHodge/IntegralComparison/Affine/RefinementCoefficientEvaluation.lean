import OAI.NumberTheory.PadicHodge.IntegralComparison.Affine.RefinementCoefficientMap

/-! # Refinement Coefficient Evaluation -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Affine.RefinementCoefficientEvaluation

noncomputable section

/-! Evaluation on coefficient sections agrees with the actual map
obtained from a common augmented resolution. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u
open OAI.NumberTheory.PadicHodge.IntegralComparison.AffineOpen.InternalHom OAI.NumberTheory.PadicHodge.IntegralComparison.Resolution.CohomologyMaps OAI.NumberTheory.PadicHodge.IntegralComparison.Affine.RefinementCoefficientMap

variable {X : Scheme.{u}} (U : X.Opens) (hU : IsAffineOpen U)
  (N : X.Modules) [N.IsQuasicoherent]
  (K L P : ChainComplex X.Modules ℕ)
  [∀ q, (K.X q).IsQuasicoherent] [∀ q, (L.X q).IsQuasicoherent] [∀ q, (P.X q).IsQuasicoherent]
  [∀ q, ((LinearResolutionPurity.internalComplex N K).X q).IsQuasicoherent]
  [∀ q, ((LinearResolutionPurity.internalComplex N L).X q).IsQuasicoherent]
  [∀ q, ((LinearResolutionPurity.internalComplex N P).X q).IsQuasicoherent]
  (M M' : X.Modules) [M.IsQuasicoherent] [M'.IsQuasicoherent]
  (ε : K ⟶ (ChainComplex.single₀ X.Modules).obj M) [QuasiIso ε]
  (ε' : L ⟶ (ChainComplex.single₀ X.Modules).obj M') [QuasiIso ε']
  (ε₀ : P ⟶ (ChainComplex.single₀ X.Modules).obj M) [QuasiIso ε₀]
  [∀ q, Projective ((AffineOpen.InternalHom.sections U hU).obj (K.X q))]
  [∀ q, Projective ((AffineOpen.InternalHom.sections U hU).obj (L.X q))]
  [∀ q, Projective ((AffineOpen.InternalHom.sections U hU).obj (P.X q))]
  (D D' : ModuleCat Γ(X, U))
  (eM : (AffineOpen.InternalHom.sections U hU).obj M ≅ D) (eM' : (AffineOpen.InternalHom.sections U hU).obj M' ≅ D')
  (f : M ⟶ M') (a : P ⟶ K) (b : P ⟶ L)
  (ha : a ≫ ε = ε₀) (hb : b ≫ ε' = ε₀ ≫ (ChainComplex.single₀ X.Modules).map f)
  (v : D ⟶ D') (hv : (AffineOpen.InternalHom.sections U hU).map f ≫ eM'.hom = eM.hom ≫ v)
  (n : ℕ)
  (d : (LinearResolutionPurity.internalComplex N L).homology n ⟶
    (LinearResolutionPurity.internalComplex N K).homology n)
  (hd : d ≫ HomologicalComplex.homologyMap (HomCohomologyNaturality.nativeMap N P K a) n =
    HomologicalComplex.homologyMap (HomCohomologyNaturality.nativeMap N P L b) n)

include ha hb hv hd in
omit [N.IsQuasicoherent] in
theorem comparison (z : Γ((LinearResolutionPurity.internalComplex N L).homology n, U)) :
    (AffinePrincipal.Cohomology.Comparison.comparison U hU N K n).hom
      ((ModuleExactSections.sections U).map d z) =
    Resolution.CohomologyMaps.map (Resolution.CohomologyMaps.homFunctor Γ(X, U) ((AffineOpen.InternalHom.sections U hU).obj N))
      (CoefficientLifts.resolution U hU K M ε D eM)
      (CoefficientLifts.resolution U hU L M' ε' D' eM') v n
      ((AffinePrincipal.Cohomology.Comparison.comparison U hU N L n).hom z) := by
  let PK := CoefficientLifts.resolution U hU K M ε D eM
  let PL := CoefficientLifts.resolution U hU L M' ε' D' eM'
  let P₀ := CoefficientLifts.resolution U hU P M ε₀ D eM
  let F := Resolution.CohomologyMaps.homFunctor Γ(X, U) ((AffineOpen.InternalHom.sections U hU).obj N)
  apply (ConcreteCategory.bijective_of_isIso (RefinementCoefficientMap.identityIso ((AffineOpen.InternalHom.sections U hU).obj N) D P₀ PK n).hom).injective
  have ha' : a ≫ ε = ε₀ ≫ (ChainComplex.single₀ X.Modules).map (𝟙 M) := by simpa using ha
  have hv' : (AffineOpen.InternalHom.sections U hU).map (𝟙 M) ≫ eM.hom = eM.hom ≫ 𝟙 D := by simp
  have hA := RefinementCoefficientMap.comparison_map U hU N P K M M ε₀ ε D D eM eM (𝟙 M) a ha' (𝟙 D) hv' n
    ((ModuleExactSections.sections U).map d z)
  have hB := RefinementCoefficientMap.comparison_map U hU N P L M M' ε₀ ε' D D' eM eM' f b hb v hv n z
  have hs := ConcreteCategory.congr_hom
    (congrArg (ModuleExactSections.sections U).map hd) z
  simp only [CategoryTheory.Functor.map_comp, ModuleCat.comp_apply] at hs
  have hc := ConcreteCategory.congr_hom (Resolution.CohomologyMaps.map_comp F P₀ PK PL (𝟙 D) v n)
    ((AffinePrincipal.Cohomology.Comparison.comparison U hU N L n).hom z)
  simp only [Category.id_comp, ModuleCat.comp_apply] at hc
  exact hA.symm.trans ((congrArg (AffinePrincipal.Cohomology.Comparison.comparison U hU N P n).hom hs).trans
    (hB.trans hc))

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Affine.RefinementCoefficientEvaluation

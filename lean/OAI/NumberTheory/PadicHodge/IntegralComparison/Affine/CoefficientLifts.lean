import OAI.NumberTheory.PadicHodge.IntegralComparison.Affine.FiniteProjectivePurity

/-! # Coefficient Lifts -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Affine.CoefficientLifts

noncomputable section

/-! Original sheaf resolution lifts remain augmentation-preserving lifts
under the native affine chart comparison and specified coefficient isomorphisms. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

set_option backward.isDefEq.respectTransparency false

universe u
open OAI.NumberTheory.PadicHodge.IntegralComparison.AffineOpen.InternalHom
variable {X : Scheme.{u}} (U : X.Opens) (hU : IsAffineOpen U)
  (K : ChainComplex X.Modules ℕ) [∀ q, (K.X q).IsQuasicoherent]
  (M : X.Modules) [M.IsQuasicoherent]
  (ε : K ⟶ (ChainComplex.single₀ X.Modules).obj M) [QuasiIso ε]
  [∀ q, Projective ((AffineOpen.InternalHom.sections U hU).obj (K.X q))]
  (D : ModuleCat Γ(X, U)) (eM : (AffineOpen.InternalHom.sections U hU).obj M ≅ D)

def resolution : ProjectiveResolution D :=
  IntegralComparison.ProjectiveResolution.Transport.alongIso
    (AffineOpen.Resolution.ofAugmentation U hU M K ε) eM

theorem augmentation_zero : (resolution U hU K M ε D eM).π.f 0 =
    (AffineOpen.InternalHom.sections U hU).map (ε.f 0) ≫ eM.hom := by
  change (((AffineOpen.InternalHom.sections U hU).mapHomologicalComplex (.down ℕ)).map ε ≫
    (HomologicalComplex.singleMapHomologicalComplex (AffineOpen.InternalHom.sections U hU) (.down ℕ) 0).hom.app M ≫
      (ChainComplex.single₀ (ModuleCat Γ(X, U))).map eM.hom).f 0 = _
  rw [HomologicalComplex.comp_f, HomologicalComplex.comp_f,
    ChainComplex.single₀_map_f_zero, HomologicalComplex.singleMapHomologicalComplex_hom_app_self]
  simp only [ChainComplex.single₀ObjXSelf, Iso.refl_hom, CategoryTheory.Functor.map_id,
    Category.id_comp]
  rfl

variable (L : ChainComplex X.Modules ℕ) [∀ q, (L.X q).IsQuasicoherent]
  (M' : X.Modules) [M'.IsQuasicoherent]
  (ε' : L ⟶ (ChainComplex.single₀ X.Modules).obj M') [QuasiIso ε']
  [∀ q, Projective ((AffineOpen.InternalHom.sections U hU).obj (L.X q))]
  (D' : ModuleCat Γ(X, U)) (eM' : (AffineOpen.InternalHom.sections U hU).obj M' ≅ D')
  (f : M ⟶ M') (a : K ⟶ L)
  (ha : a ≫ ε' = ε ≫ (ChainComplex.single₀ X.Modules).map f)
  (u : D ⟶ D') (hu : (AffineOpen.InternalHom.sections U hU).map f ≫ eM'.hom = eM.hom ≫ u)

include ha hu in
theorem augmentation :
    ((AffineOpen.InternalHom.sections U hU).mapHomologicalComplex (.down ℕ)).map a ≫
      (resolution U hU L M' ε' D' eM').π =
    (resolution U hU K M ε D eM).π ≫ (ChainComplex.single₀ (ModuleCat Γ(X, U))).map u := by
  apply (ChainComplex.toSingle₀Equiv _ _).injective
  apply Subtype.ext
  change (((AffineOpen.InternalHom.sections U hU).mapHomologicalComplex (.down ℕ)).map a ≫
    (resolution U hU L M' ε' D' eM').π).f 0 =
    ((resolution U hU K M ε D eM).π ≫ (ChainComplex.single₀ (ModuleCat Γ(X, U))).map u).f 0
  rw [HomologicalComplex.comp_f, HomologicalComplex.comp_f, augmentation_zero,
    augmentation_zero, ChainComplex.single₀_map_f_zero]
  have ha0 := congrArg (fun t => t.f 0) ha
  simp only [HomologicalComplex.comp_f, ChainComplex.single₀_map_f_zero] at ha0
  change (AffineOpen.InternalHom.sections U hU).map (a.f 0) ≫ ((AffineOpen.InternalHom.sections U hU).map (ε'.f 0) ≫ eM'.hom) = _
  rw [← Category.assoc, ← CategoryTheory.Functor.map_comp, ha0,
    CategoryTheory.Functor.map_comp, Category.assoc, hu, ← Category.assoc]

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Affine.CoefficientLifts

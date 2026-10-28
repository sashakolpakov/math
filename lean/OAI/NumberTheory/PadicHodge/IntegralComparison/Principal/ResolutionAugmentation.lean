import OAI.NumberTheory.PadicHodge.IntegralComparison.Principal.Resolution

/-! # Resolution Augmentation -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Principal.ResolutionAugmentation

noncomputable section

/-! Actual sheaf augmentation squares induce the exact quotient
augmentation squares used by principal-open resolution comparison. -/
open _root_.CategoryTheory _root_.AlgebraicGeometry
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open OAI.NumberTheory.PadicHodge.IntegralComparison.AffineOpen.InternalHom OAI.NumberTheory.PadicHodge.IntegralComparison.Principal.Resolution.Comparison
variable {X : Scheme.{u}} (U : X.Opens) (hU : IsAffineOpen U)
  (M : X.Modules) [M.IsQuasicoherent]
  (K : ChainComplex X.Modules ℕ) [∀ q, (K.X q).IsQuasicoherent]
  (ε : K ⟶ (ChainComplex.single₀ X.Modules).obj M) [QuasiIso ε]
  [∀ q, Projective ((AffineOpen.InternalHom.sections U hU).obj (K.X q))]
  (T : ModuleCat.{u} Γ(X, U)) (eM : (AffineOpen.InternalHom.sections U hU).obj M ≅ T)

theorem zero : (Resolution.Comparison.resolution U hU M K ε T eM).π.f 0 =
    (AffineOpen.InternalHom.sections U hU).map (ε.f 0) ≫ eM.hom := by
  change (((AffineOpen.InternalHom.sections U hU).mapHomologicalComplex (.down ℕ)).map ε ≫
    (HomologicalComplex.singleMapHomologicalComplex (AffineOpen.InternalHom.sections U hU) (.down ℕ) 0).hom.app M ≫
      (ChainComplex.single₀ (ModuleCat Γ(X, U))).map eM.hom).f 0 = _
  rw [HomologicalComplex.comp_f, HomologicalComplex.comp_f,
    ChainComplex.single₀_map_f_zero, HomologicalComplex.singleMapHomologicalComplex_hom_app_self]
  simp only [ChainComplex.single₀ObjXSelf, Iso.refl_hom, CategoryTheory.Functor.map_id,
    Category.id_comp]
  rfl

variable (M' : X.Modules) [M'.IsQuasicoherent]
  (L : ChainComplex X.Modules ℕ) [∀ q, (L.X q).IsQuasicoherent]
  (ε' : L ⟶ (ChainComplex.single₀ X.Modules).obj M') [QuasiIso ε']
  [∀ q, Projective ((AffineOpen.InternalHom.sections U hU).obj (L.X q))]
  (T' : ModuleCat.{u} Γ(X, U)) (eM' : (AffineOpen.InternalHom.sections U hU).obj M' ≅ T')
  (f : K ⟶ L) (v : M ⟶ M') (b : T ⟶ T')
  (hf : f ≫ ε' = ε ≫ (ChainComplex.single₀ X.Modules).map v)
  (hv : (AffineOpen.InternalHom.sections U hU).map v ≫ eM'.hom = eM.hom ≫ b)

include hf hv in
theorem square : (((AffineOpen.InternalHom.sections U hU).mapHomologicalComplex (.down ℕ)).map f) ≫
      (Resolution.Comparison.resolution U hU M' L ε' T' eM').π =
    (Resolution.Comparison.resolution U hU M K ε T eM).π ≫ (ChainComplex.single₀ _).map b := by
  apply (ChainComplex.toSingle₀Equiv _ _).injective
  apply Subtype.ext
  change (((AffineOpen.InternalHom.sections U hU).mapHomologicalComplex (.down ℕ)).map f).f 0 ≫
      (Resolution.Comparison.resolution U hU M' L ε' T' eM').π.f 0 =
    (Resolution.Comparison.resolution U hU M K ε T eM).π.f 0 ≫ b
  rw [zero, zero]
  have h := congrArg (fun a => a.f 0) hf
  change f.f 0 ≫ ε'.f 0 = ε.f 0 ≫ v at h
  change (AffineOpen.InternalHom.sections U hU).map (f.f 0) ≫ ((AffineOpen.InternalHom.sections U hU).map (ε'.f 0) ≫ eM'.hom) = _
  rw [← Category.assoc, ← CategoryTheory.Functor.map_comp, h,
    CategoryTheory.Functor.map_comp, Category.assoc, hv, ← Category.assoc]

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Principal.ResolutionAugmentation

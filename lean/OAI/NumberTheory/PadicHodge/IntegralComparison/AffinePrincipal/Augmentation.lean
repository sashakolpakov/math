import OAI.NumberTheory.PadicHodge.IntegralComparison.Affine.OrientedPurity
import OAI.NumberTheory.PadicHodge.IntegralComparison.AffinePrincipal.Hom

/-! # Augmentation -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.AffinePrincipal.Augmentation

noncomputable section

/-! The original affine projective resolutions have the required
augmentation square under principal restriction. The only coefficient
condition is the literal normalization square for the resolved quotient. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry Opposite
open scoped TensorProduct

open OAI.NumberTheory.PadicHodge.IntegralComparison.AffinePrincipal.Sections OAI.NumberTheory.PadicHodge.IntegralComparison.AffineOpen.InternalHom

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

universe u

variable {X : Scheme.{u}} (U : X.Opens) (hU : IsAffineOpen U) (r : Γ(X, U))

theorem chart_naturality {M N : X.Modules} [M.IsQuasicoherent] [N.IsQuasicoherent]
    (f : M ⟶ N) :
    (Hom.Comparison.chartIso U hU r M).hom ≫
        (AffineOpen.InternalHom.sections (Sections.openSubset U r) (hU.basicOpen r)).map f =
      (PrincipalComplex.tensorFunctor U r).map ((AffineOpen.InternalHom.sections U hU).map f) ≫
        (Hom.Comparison.chartIso U hU r N).hom := by
  let T := PrincipalComplex.tensorFunctor U r
  have hP :
      T.map ((Affine.ModuleExactSections.sections U).map f) ≫
          (Sections.iso U hU r N).toModuleIso.hom =
        (Sections.iso U hU r M).toModuleIso.hom ≫
          (Affine.ModuleExactSections.sections (Sections.openSubset U r)).map f := by
    apply ConcreteCategory.hom_ext
    intro x
    exact Sections.naturality U hU r f x
  have hU' := (AffineOpen.LinearHom.sectionsIso U hU).inv.naturality f
  have hV' := (AffineOpen.LinearHom.sectionsIso (Sections.openSubset U r) (hU.basicOpen r)).hom.naturality f
  change (T.map (Affine.ChartSections.iso U hU M).inv ≫
      (Sections.iso U hU r M).toModuleIso.hom ≫
        (Affine.ChartSections.iso (Sections.openSubset U r) (hU.basicOpen r) M).hom) ≫ _ =
    T.map ((AffineOpen.InternalHom.sections U hU).map f) ≫
      (T.map (Affine.ChartSections.iso U hU N).inv ≫
        (Sections.iso U hU r N).toModuleIso.hom ≫
          (Affine.ChartSections.iso (Sections.openSubset U r) (hU.basicOpen r) N).hom)
  change (AffineOpen.InternalHom.sections U hU).map f ≫ (Affine.ChartSections.iso U hU N).inv =
    (Affine.ChartSections.iso U hU M).inv ≫ (Affine.ModuleExactSections.sections U).map f at hU'
  change (Affine.ModuleExactSections.sections (Sections.openSubset U r)).map f ≫
      (Affine.ChartSections.iso (Sections.openSubset U r) (hU.basicOpen r) N).hom =
    (Affine.ChartSections.iso (Sections.openSubset U r) (hU.basicOpen r) M).hom ≫
      (AffineOpen.InternalHom.sections (Sections.openSubset U r) (hU.basicOpen r)).map f at hV'
  simp only [Category.assoc]
  rw [← hV']
  have hp := congrArg (fun a => T.map (Affine.ChartSections.iso U hU M).inv ≫ a ≫
    (Affine.ChartSections.iso (Sections.openSubset U r) (hU.basicOpen r) N).hom) hP.symm
  have hu := congrArg (fun a => T.map a ≫ (Sections.iso U hU r N).toModuleIso.hom ≫
    (Affine.ChartSections.iso (Sections.openSubset U r) (hU.basicOpen r) N).hom) hU'.symm
  simp only [CategoryTheory.Functor.map_comp, Category.assoc] at hp hu
  exact hp.trans hu

variable (K : ChainComplex X.Modules ℕ) [∀ q, (K.X q).IsQuasicoherent]
  (M : X.Modules) [M.IsQuasicoherent]
  (ε : K ⟶ (ChainComplex.single₀ X.Modules).obj M) [QuasiIso ε]
  [∀ q, Projective ((AffineOpen.InternalHom.sections U hU).obj (K.X q))]

theorem augmentation_zero (I : Ideal Γ(X, U))
    (eM : (AffineOpen.InternalHom.sections U hU).obj M ≅ ModuleCat.of Γ(X, U) (Γ(X, U) ⧸ I)) :
    (Affine.OrientedPurity.resolution U hU K M ε I eM).π.f 0 =
      (AffineOpen.InternalHom.sections U hU).map (ε.f 0) ≫ eM.hom := by
  change (((AffineOpen.InternalHom.sections U hU).mapHomologicalComplex (.down ℕ)).map ε ≫
    (HomologicalComplex.singleMapHomologicalComplex (AffineOpen.InternalHom.sections U hU) (.down ℕ) 0).hom.app M ≫
      (ChainComplex.single₀ (ModuleCat Γ(X, U))).map eM.hom).f 0 = _
  rw [HomologicalComplex.comp_f, HomologicalComplex.comp_f,
    ChainComplex.single₀_map_f_zero, HomologicalComplex.singleMapHomologicalComplex_hom_app_self]
  simp only [ChainComplex.single₀ObjXSelf, Iso.refl_hom, CategoryTheory.Functor.map_id,
    Category.id_comp]
  rfl

variable [∀ q, Projective ((AffineOpen.InternalHom.sections (Sections.openSubset U r) (hU.basicOpen r)).obj (K.X q))]
  (I : Ideal Γ(X, U)) (J : Ideal Γ(X, Sections.openSubset U r))
  (eM : (AffineOpen.InternalHom.sections U hU).obj M ≅ ModuleCat.of Γ(X, U) (Γ(X, U) ⧸ I))
  (eM' : (AffineOpen.InternalHom.sections (Sections.openSubset U r) (hU.basicOpen r)).obj M ≅
    ModuleCat.of Γ(X, Sections.openSubset U r) (Γ(X, Sections.openSubset U r) ⧸ J))
  (q : (PrincipalComplex.tensorFunctor U r).obj
      (ModuleCat.of Γ(X, U) (Γ(X, U) ⧸ I)) ⟶
    ModuleCat.of Γ(X, Sections.openSubset U r) (Γ(X, Sections.openSubset U r) ⧸ J))

theorem augmentation_square
    (he : (Hom.Comparison.chartIso U hU r M).hom ≫ eM'.hom =
      (PrincipalComplex.tensorFunctor U r).map eM.hom ≫ q) :
    (PrincipalComplex.chartIso U hU r (.down ℕ) K).hom.f 0 ≫
        (Affine.OrientedPurity.resolution (Sections.openSubset U r) (hU.basicOpen r) K M ε J eM').π.f 0 =
      (PrincipalComplex.tensorFunctor U r).map
        ((Affine.OrientedPurity.resolution U hU K M ε I eM).π.f 0) ≫ q := by
  have hC : (PrincipalComplex.chartIso U hU r (.down ℕ) K).hom.f 0 =
      (Hom.Comparison.chartIso U hU r (K.X 0)).hom := rfl
  have hn := chart_naturality U hU r (show K.X 0 ⟶ M from ε.f 0)
  rw [hC, augmentation_zero, augmentation_zero, ← Category.assoc, hn,
    Category.assoc, he, ← Category.assoc, ← CategoryTheory.Functor.map_comp]

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.AffinePrincipal.Augmentation

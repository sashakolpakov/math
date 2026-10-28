import OAI.AlgebraicGeometry.FormalGeometry.Completion.GlobalSectionCechPullback
import OAI.AlgebraicGeometry.Quotients.FiniteDescent.OrderedCechZeroGluing

/-! # Global Section Composition -/

namespace OAI.AlgebraicGeometry.FormalGeometry.Completion.GlobalSectionComposition

noncomputable section

/-! Actual global section pullback through the sheaf composition
isomorphism, and detection of equality on ordered Cech coordinates. -/

set_option backward.isDefEq.respectTransparency false

open _root_.AlgebraicGeometry _root_.CategoryTheory _root_.CategoryTheory.Limits Opposite
open _root_.AlgebraicGeometry.Scheme.Modules

namespace Construction

universe u

def globalSectionCompositePullback {X Y Z : Scheme.{u}} (f : Y ⟶ X) (j : Z ⟶ Y)
    (M : X.Modules) (s : Γ((Scheme.Modules.pullback f).obj M, ⊤)) :
    Γ((Scheme.Modules.pullback (j ≫ f)).obj M, ⊤) :=
  ((Scheme.Modules.pullbackComp j f).hom.app M).app ⊤
    (GlobalSectionCechPullback.Construction.globalLineSectionPullback j ((Scheme.Modules.pullback f).obj M) s)

theorem globalSectionCompositePullback_restriction {X Y Z : Scheme.{u}}
    (f : Y ⟶ X) (j : Z ⟶ Y) (M : X.Modules)
    (V : Y.Opens) (W : Z.Opens) (hW : W ≤ j ⁻¹ᵁ V)
    (s : Γ((Scheme.Modules.pullback f).obj M, ⊤)) :
    ((Scheme.Modules.pullback (j ≫ f)).obj M).presheaf.map (homOfLE (show W ≤ ⊤ from le_top)).op
      (globalSectionCompositePullback f j M s) =
    ((Scheme.Modules.pullbackComp j f).hom.app M).app W
      (Quotients.FiniteDescent.RestrictedPullback.Construction.RestrictedPullbackSections.map j ((Scheme.Modules.pullback f).obj M) V W hW
        (((Scheme.Modules.pullback f).obj M).presheaf.map (homOfLE (show V ≤ ⊤ from le_top)).op s)) := by
  have hn := PresheafOfModules.naturality_apply ((Scheme.Modules.pullbackComp j f).hom.app M).val
    (homOfLE (show W ≤ ⊤ from le_top)).op
    (GlobalSectionCechPullback.Construction.globalLineSectionPullback j ((Scheme.Modules.pullback f).obj M) s)
  exact hn.symm.trans (congrArg (((Scheme.Modules.pullbackComp j f).hom.app M).app W)
    (GlobalSectionCechPullback.Construction.restrictedPullbackSection_restriction j ((Scheme.Modules.pullback f).obj M)
      le_top le_top (by simp) hW s))

private theorem product_ext {R : Type u} [CommRing R] {I : Type u}
    (A : I → ModuleCat.{u} R) {x y : (∏ᶜ A : ModuleCat.{u} R)}
    (h : ∀ i, Pi.π A i x = Pi.π A i y) : x = y := by
  apply (ModuleCat.piIsoPi A).toLinearEquiv.injective
  funext i
  exact (ConcreteCategory.congr_hom (ModuleCat.piIsoPi_hom_ker_subtype A i) x).trans
    ((h i).trans (ConcreteCategory.congr_hom (ModuleCat.piIsoPi_hom_ker_subtype A i) y).symm)

theorem globalSections_ext_cechCoordinates {X S : Scheme.{u}} (π : X ⟶ S) (M : X.Modules)
    {ι : Type u} [LinearOrder ι] (U : ι → X.Opens) (hU : iSup U = ⊤)
    (s s' : (SheafCohomology.Cech.SchemeModuleBaseBasic.Scheme.Modules.baseModulePresheaf π M).obj (op ⊤))
    (hs : ∀ i : SheafCohomology.Projective.OrderedBaseCech.Scheme.Modules.OrderedCechIndex ι 0,
      M.presheaf.map (homOfLE (show (∏ᶜ fun k => U (i.1 k)) ≤ ⊤ from le_top)).op s =
      M.presheaf.map (homOfLE (show (∏ᶜ fun k => U (i.1 k)) ≤ ⊤ from le_top)).op s') : s = s' := by
  apply (Quotients.FiniteDescent.OrderedCechZeroGluing.Construction.OrderedCechZeroCoordinates.sectionsEquiv π M U hU).injective
  apply Subtype.ext
  apply product_ext (fun i : SheafCohomology.Projective.OrderedBaseCech.Scheme.Modules.OrderedCechIndex ι 0 => SheafCohomology.Cech.SchemeModuleBaseBasic.Scheme.Modules.baseCechFactor π M U 0 i.1)
  intro i
  exact (Quotients.FiniteDescent.OrderedCechZeroGluing.Construction.OrderedCechZeroCoordinates.sectionsEquiv_π π M U hU s i).trans
    ((hs i).trans (Quotients.FiniteDescent.OrderedCechZeroGluing.Construction.OrderedCechZeroCoordinates.sectionsEquiv_π π M U hU s' i).symm)

end Construction

end

end OAI.AlgebraicGeometry.FormalGeometry.Completion.GlobalSectionComposition

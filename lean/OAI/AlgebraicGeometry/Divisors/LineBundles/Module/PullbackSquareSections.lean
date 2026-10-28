import OAI.AlgebraicGeometry.Divisors.LineBundles.Module.SectionPullbackComposition

/-! # Pullback Square Sections -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.Module.PullbackSquareSections.BundleCycles

noncomputable section

section

/-! # LineBundleCycles: source restriction and equality transport for actual section pullbacks to open subsets -/

open _root_.AlgebraicGeometry _root_.CategoryTheory

variable {X Y : Scheme.{0}} (f : X ⟶ Y) (M : Y.Modules)

theorem moduleSectionPullbackToOpen_restrict_source {U W : Y.Opens} (hWU : W ≤ U)
    (V : X.Opens) (hV : V ≤ f ⁻¹ᵁ W) (s : Γ(M, U)) :
    SectionPullbackComposition.BundleCycles.moduleSectionPullbackToOpen f M W V hV (M.presheaf.map (homOfLE hWU).op s) =
      SectionPullbackComposition.BundleCycles.moduleSectionPullbackToOpen f M U V (fun _ hx => hWU (hV hx)) s := by
  have H := congrArg (((Scheme.Modules.pullback f).obj M).presheaf.map (homOfLE hV).op)
    (OpenPullbackSections.BundleCycles.moduleSectionPullbackOnOpen_restrict f M hWU s)
  rw [← ConcreteCategory.comp_apply, ← Functor.map_comp] at H
  exact H.symm

theorem moduleSectionPullbackToOpen_congr {f g : X ⟶ Y} (hfg : f = g)
    (U : Y.Opens) (V : X.Opens) (hf : V ≤ f ⁻¹ᵁ U) (hg : V ≤ g ⁻¹ᵁ U) (s : Γ(M, U)) :
    ((Scheme.Modules.pullbackCongr hfg).hom.app M).app V
      (SectionPullbackComposition.BundleCycles.moduleSectionPullbackToOpen f M U V hf s) = SectionPullbackComposition.BundleCycles.moduleSectionPullbackToOpen g M U V hg s := by
  subst g
  rfl

end

/-! # LineBundleCycles: the actual pullback isomorphism of a commutative square preserves local sections -/

open _root_.AlgebraicGeometry _root_.CategoryTheory

variable {X Y Z W : Scheme.{0}} (f : Y ⟶ X) (q : W ⟶ Y) (i : Z ⟶ X) (j : W ⟶ Z)
    (h : q ≫ f = j ≫ i) (M : X.Modules)

def modulePullbackSquareIso :
    (Scheme.Modules.pullback q).obj ((Scheme.Modules.pullback f).obj M) ≅
      (Scheme.Modules.pullback j).obj ((Scheme.Modules.pullback i).obj M) :=
  (Scheme.Modules.pullbackComp q f).app M ≪≫
    (Scheme.Modules.pullbackCongr h).app M ≪≫ ((Scheme.Modules.pullbackComp j i).app M).symm

theorem modulePullbackSquareIso_section (U : X.Opens) (V : W.Opens)
    (hq : V ≤ (q ≫ f) ⁻¹ᵁ U) (hj : V ≤ (j ≫ i) ⁻¹ᵁ U) (s : Γ(M, U)) :
    (modulePullbackSquareIso f q i j h M).hom.app V
      (SectionPullbackComposition.BundleCycles.moduleSectionPullbackToOpen q ((Scheme.Modules.pullback f).obj M) (f ⁻¹ᵁ U) V hq
        (OpenPullbackSections.BundleCycles.moduleSectionPullbackOnOpen f M U s)) =
      SectionPullbackComposition.BundleCycles.moduleSectionPullbackToOpen j ((Scheme.Modules.pullback i).obj M) (i ⁻¹ᵁ U) V hj
        (OpenPullbackSections.BundleCycles.moduleSectionPullbackOnOpen i M U s) := by
  let e₁ := (Scheme.Modules.pullbackComp q f).app M
  let e₂ := (Scheme.Modules.pullbackCongr h).app M
  let e₃ := ((Scheme.Modules.pullbackComp j i).app M).symm
  have H₁ := SectionPullbackComposition.BundleCycles.moduleSectionPullbackToOpen_comp_hom q f M U V hq s
  have H₂ := moduleSectionPullbackToOpen_congr M h U V hq hj s
  have H₃ := SectionPullbackComposition.BundleCycles.moduleSectionPullbackToOpen_comp_inv j i M U V hj s
  exact (congrArg (fun z => e₃.hom.app V z)
    ((congrArg (fun z => e₂.hom.app V z) H₁).trans H₂)).trans H₃

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.Module.PullbackSquareSections.BundleCycles

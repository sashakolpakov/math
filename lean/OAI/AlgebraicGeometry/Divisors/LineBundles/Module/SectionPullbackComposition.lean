import OAI.AlgebraicGeometry.Divisors.LineBundles.Module.OpenPullbackSections

/-! # Section Pullback Composition -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.Module.SectionPullbackComposition.BundleCycles

noncomputable section

section

/-! # LineBundleCycles: composition of actual module-section pullbacks through the canonical pullback isomorphism -/

open _root_.AlgebraicGeometry _root_.CategoryTheory

variable {X Y Z : Scheme.{0}} (f : X ⟶ Y) (g : Y ⟶ Z) (M : Z.Modules)

theorem moduleSectionPullback_comp_inv (U : Z.Opens) (s : Γ(M, U)) :
    ((Scheme.Modules.pullbackComp f g).inv.app M).app ((f ≫ g) ⁻¹ᵁ U)
      (OpenPullbackSections.BundleCycles.moduleSectionPullbackOnOpen (f ≫ g) M U s) =
      OpenPullbackSections.BundleCycles.moduleSectionPullbackOnOpen f ((Scheme.Modules.pullback g).obj M) (g ⁻¹ᵁ U)
        (OpenPullbackSections.BundleCycles.moduleSectionPullbackOnOpen g M U s) := by
  have H := unit_conjugateEquiv
    ((Scheme.Modules.pullbackPushforwardAdjunction g).comp (Scheme.Modules.pullbackPushforwardAdjunction f))
    (Scheme.Modules.pullbackPushforwardAdjunction (f ≫ g)) (Scheme.Modules.pullbackComp f g).inv M
  rw [Scheme.Modules.conjugateEquiv_pullbackComp_inv, Adjunction.comp_unit_app] at H
  exact (congrArg (fun k => k.app U s) H).symm

theorem moduleSectionPullback_comp_hom (U : Z.Opens) (s : Γ(M, U)) :
    ((Scheme.Modules.pullbackComp f g).hom.app M).app ((f ≫ g) ⁻¹ᵁ U)
      (OpenPullbackSections.BundleCycles.moduleSectionPullbackOnOpen f ((Scheme.Modules.pullback g).obj M) (g ⁻¹ᵁ U)
        (OpenPullbackSections.BundleCycles.moduleSectionPullbackOnOpen g M U s)) =
      OpenPullbackSections.BundleCycles.moduleSectionPullbackOnOpen (f ≫ g) M U s := by
  rw [← moduleSectionPullback_comp_inv f g M U s]
  exact ConcreteCategory.congr_hom
    (congrArg (fun k => k.app ((f ≫ g) ⁻¹ᵁ U)) ((Scheme.Modules.pullbackComp f g).app M).inv_hom_id) _

end

/-! # LineBundleCycles: actual section pullback followed by restriction to a specified smaller open -/

open _root_.AlgebraicGeometry _root_.CategoryTheory

variable {X Y : Scheme.{0}} (f : X ⟶ Y) (M : Y.Modules)

def moduleSectionPullbackToOpen (U : Y.Opens) (V : X.Opens) (hV : V ≤ f ⁻¹ᵁ U)
    (s : Γ(M, U)) : Γ((Scheme.Modules.pullback f).obj M, V) :=
  ((Scheme.Modules.pullback f).obj M).presheaf.map (homOfLE hV).op (OpenPullbackSections.BundleCycles.moduleSectionPullbackOnOpen f M U s)

theorem moduleSectionPullbackToOpen_restrict (U : Y.Opens) {V W : X.Opens}
    (hW : W ≤ V) (hV : V ≤ f ⁻¹ᵁ U) (s : Γ(M, U)) :
    ((Scheme.Modules.pullback f).obj M).presheaf.map (homOfLE hW).op
      (moduleSectionPullbackToOpen f M U V hV s) = moduleSectionPullbackToOpen f M U W (hW.trans hV) s := by
  unfold moduleSectionPullbackToOpen
  rw [← ConcreteCategory.comp_apply, ← Functor.map_comp]
  rfl

theorem moduleSectionPullbackToOpen_naturality {M N : Y.Modules} (φ : M ⟶ N)
    (U : Y.Opens) (V : X.Opens) (hV : V ≤ f ⁻¹ᵁ U) (s : Γ(M, U)) :
    ((Scheme.Modules.pullback f).map φ).app V (moduleSectionPullbackToOpen f M U V hV s) =
      moduleSectionPullbackToOpen f N U V hV (φ.app U s) := by
  have H := ConcreteCategory.congr_hom
    (((Scheme.Modules.pullback f).map φ).mapPresheaf.naturality (homOfLE hV).op)
    (OpenPullbackSections.BundleCycles.moduleSectionPullbackOnOpen f M U s)
  exact H.trans (congrArg (((Scheme.Modules.pullback f).obj N).presheaf.map (homOfLE hV).op)
    (OpenPullbackSections.BundleCycles.moduleSectionPullbackOnOpen_naturality f φ U s))

variable {Z : Scheme.{0}} (g : Y ⟶ Z) (N : Z.Modules)

theorem moduleSectionPullbackToOpen_comp_inv (U : Z.Opens) (V : X.Opens)
    (hV : V ≤ (f ≫ g) ⁻¹ᵁ U) (s : Γ(N, U)) :
    ((Scheme.Modules.pullbackComp f g).inv.app N).app V
      (moduleSectionPullbackToOpen (f ≫ g) N U V hV s) =
      moduleSectionPullbackToOpen f ((Scheme.Modules.pullback g).obj N) (g ⁻¹ᵁ U) V hV
        (OpenPullbackSections.BundleCycles.moduleSectionPullbackOnOpen g N U s) := by
  have H := ConcreteCategory.congr_hom
    (((Scheme.Modules.pullbackComp f g).inv.app N).mapPresheaf.naturality (homOfLE hV).op)
    (OpenPullbackSections.BundleCycles.moduleSectionPullbackOnOpen (f ≫ g) N U s)
  exact H.trans (congrArg (((Scheme.Modules.pullback f).obj ((Scheme.Modules.pullback g).obj N)).presheaf.map
    (homOfLE hV).op) (moduleSectionPullback_comp_inv f g N U s))

theorem moduleSectionPullbackToOpen_comp_hom (U : Z.Opens) (V : X.Opens)
    (hV : V ≤ (f ≫ g) ⁻¹ᵁ U) (s : Γ(N, U)) :
    ((Scheme.Modules.pullbackComp f g).hom.app N).app V
      (moduleSectionPullbackToOpen f ((Scheme.Modules.pullback g).obj N) (g ⁻¹ᵁ U) V hV
        (OpenPullbackSections.BundleCycles.moduleSectionPullbackOnOpen g N U s)) = moduleSectionPullbackToOpen (f ≫ g) N U V hV s := by
  rw [← moduleSectionPullbackToOpen_comp_inv f g N U V hV s]
  exact ConcreteCategory.congr_hom
    (congrArg (fun k => k.app V) ((Scheme.Modules.pullbackComp f g).app N).inv_hom_id) _

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.Module.SectionPullbackComposition.BundleCycles

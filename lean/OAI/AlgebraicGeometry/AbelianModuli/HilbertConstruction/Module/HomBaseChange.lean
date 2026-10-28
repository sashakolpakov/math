import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Module.HomPresheaf

/-! # Hom Base Change -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Module.HomBaseChange

noncomputable section

/-! The presheaf of module maps is compatible with changing the base scheme. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

variable {X Y : Scheme.{u}}

def moduleHomBaseChangeEquiv (g : Y ⟶ X) (M N : X.Modules) (T : Over Y) :
    (HomPresheaf.moduleHomPresheaf ((Scheme.Modules.pullback g).obj M) ((Scheme.Modules.pullback g).obj N)).obj
        (.op T) ≃
      (HomPresheaf.moduleHomPresheaf M N).obj (.op ((Over.map g).obj T)) :=
  Iso.homCongr ((Scheme.Modules.pullbackComp T.hom g).app M)
    ((Scheme.Modules.pullbackComp T.hom g).app N)

theorem moduleHomBaseChange_naturality {U V : Scheme.{u}} (a : U ⟶ V) (f : V ⟶ Y)
    (g : Y ⟶ X) (M N : X.Modules)
    (φ : (Scheme.Modules.pullback f).obj ((Scheme.Modules.pullback g).obj M) ⟶
      (Scheme.Modules.pullback f).obj ((Scheme.Modules.pullback g).obj N)) :
    Iso.homCongr ((Scheme.Modules.pullbackComp (a ≫ f) g).app M)
        ((Scheme.Modules.pullbackComp (a ≫ f) g).app N) (MapPullbackComposition.moduleMapPullbackComp a f φ) =
      MapPullbackCongruence.moduleMapPullbackCongr (Category.assoc a f g).symm
        (MapPullbackComposition.moduleMapPullbackComp a (f ≫ g)
          (Iso.homCongr ((Scheme.Modules.pullbackComp f g).app M)
            ((Scheme.Modules.pullbackComp f g).app N) φ)) := by
  unfold MapPullbackCongruence.moduleMapPullbackCongr MapPullbackComposition.moduleMapPullbackComp
  rw [Functor.map_homCongr]
  rw [MapPullbackComposition.moduleMap_homCongr_combine, MapPullbackComposition.moduleMap_homCongr_combine, MapPullbackComposition.moduleMap_homCongr_combine]
  rw [Pullback.AssociativityFusion.modulePullback_associativity_fusion, Pullback.AssociativityFusion.modulePullback_associativity_fusion]

theorem moduleHomBaseChangeEquiv_naturality (g : Y ⟶ X) (M N : X.Modules) {U V : Over Y}
    (a : U ⟶ V)
    (φ : (HomPresheaf.moduleHomPresheaf ((Scheme.Modules.pullback g).obj M)
      ((Scheme.Modules.pullback g).obj N)).obj (.op V)) :
    moduleHomBaseChangeEquiv g M N U (MapSlicePullback.moduleMapPullbackAlong a φ) =
      MapSlicePullback.moduleMapPullbackAlong ((Over.map g).map a) (moduleHomBaseChangeEquiv g M N V φ) := by
  change (Scheme.Modules.pullback V.hom).obj ((Scheme.Modules.pullback g).obj M) ⟶
    (Scheme.Modules.pullback V.hom).obj ((Scheme.Modules.pullback g).obj N) at φ
  obtain ⟨U, fU, rfl⟩ := U.mk_surjective
  obtain ⟨a, ha, rfl⟩ := Over.homMk_surjective a
  change U ⟶ V.left at a
  change a ≫ V.hom = fU at ha
  subst fU
  change Iso.homCongr ((Scheme.Modules.pullbackComp (a ≫ V.hom) g).app M)
      ((Scheme.Modules.pullbackComp (a ≫ V.hom) g).app N)
      (MapPullbackCongruence.moduleMapPullbackCongr rfl (MapPullbackComposition.moduleMapPullbackComp a V.hom φ)) = _
  rw [MapPullbackCongruence.moduleMapPullbackCongr_refl]
  exact moduleHomBaseChange_naturality a V.hom g M N φ

def moduleHomBaseChangeIso (g : Y ⟶ X) (M N : X.Modules) :
    HomPresheaf.moduleHomPresheaf ((Scheme.Modules.pullback g).obj M) ((Scheme.Modules.pullback g).obj N) ≅
      (Over.map g).op ⋙ HomPresheaf.moduleHomPresheaf M N :=
  NatIso.ofComponents (fun T => (moduleHomBaseChangeEquiv g M N T.unop).toIso) (by
    intro U V f
    apply ConcreteCategory.hom_ext
    intro φ
    exact moduleHomBaseChangeEquiv_naturality g M N f.unop φ)

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Module.HomBaseChange

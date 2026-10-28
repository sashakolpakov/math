import OAI.AlgebraicGeometry.FormalGeometry.Completion.PullbackSectionComposition
import OAI.AlgebraicGeometry.Quotients.FiniteDescent.PullbackSectionCongr

/-! # Pullback Structure Comparison -/

namespace OAI.AlgebraicGeometry.FormalGeometry.Completion.PullbackStructureComparison

noncomputable section

/-! Canonical structure-module frames and actual section morphisms
respect the comparison attached to a commuting square. -/

set_option backward.isDefEq.respectTransparency false

open _root_.AlgebraicGeometry _root_.CategoryTheory

namespace Construction

universe u

theorem pullbackSection_id {X Y : Scheme.{u}} (f : X ⟶ Y) :
    AbelianModuli.HilbertConstruction.Ample.LineBundles.pullbackSection f (𝟙 (AbelianModuli.HilbertConstruction.Line.Bundles.structureModule Y)) = (AbelianModuli.HilbertConstruction.Line.Bundles.structureModulePullbackIso f).inv :=
  (congrArg (fun z => (AbelianModuli.HilbertConstruction.Line.Bundles.structureModulePullbackIso f).inv ≫ z)
    ((Scheme.Modules.pullback f).map_id (AbelianModuli.HilbertConstruction.Line.Bundles.structureModule Y))).trans (Category.comp_id _)

@[reassoc]
theorem structureModulePullbackIso_comp {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) :
    (Scheme.Modules.pullbackComp f g).hom.app (AbelianModuli.HilbertConstruction.Line.Bundles.structureModule Z) ≫ (AbelianModuli.HilbertConstruction.Line.Bundles.structureModulePullbackIso (f ≫ g)).hom =
      (Scheme.Modules.pullback f).map (AbelianModuli.HilbertConstruction.Line.Bundles.structureModulePullbackIso g).hom ≫ (AbelianModuli.HilbertConstruction.Line.Bundles.structureModulePullbackIso f).hom := by
  let a := (Scheme.Modules.pullback f).mapIso (AbelianModuli.HilbertConstruction.Line.Bundles.structureModulePullbackIso g) ≪≫ AbelianModuli.HilbertConstruction.Line.Bundles.structureModulePullbackIso f
  have h := PullbackSectionComposition.Construction.pullbackSection_comp g f (AbelianModuli.HilbertConstruction.Line.Bundles.structureModule Z) (𝟙 (AbelianModuli.HilbertConstruction.Line.Bundles.structureModule Z))
  rw [pullbackSection_id, pullbackSection_id] at h
  change a.inv ≫ (Scheme.Modules.pullbackComp f g).hom.app (AbelianModuli.HilbertConstruction.Line.Bundles.structureModule Z) =
    (AbelianModuli.HilbertConstruction.Line.Bundles.structureModulePullbackIso (f ≫ g)).inv at h
  have he := congrArg (fun z => a.hom ≫ z ≫ (AbelianModuli.HilbertConstruction.Line.Bundles.structureModulePullbackIso (f ≫ g)).hom) h
  simp only [Category.assoc, Iso.hom_inv_id_assoc, Iso.inv_hom_id, Category.comp_id] at he
  exact he

@[reassoc]
theorem pullbackSection_targetMap {X Y : Scheme.{u}} (f : X ⟶ Y) {M N : Y.Modules}
    (s : AbelianModuli.HilbertConstruction.Line.Bundles.structureModule Y ⟶ M) (a : M ⟶ N) :
    AbelianModuli.HilbertConstruction.Ample.LineBundles.pullbackSection f (s ≫ a) = AbelianModuli.HilbertConstruction.Ample.LineBundles.pullbackSection f s ≫ (Scheme.Modules.pullback f).map a := by
  simp only [AbelianModuli.HilbertConstruction.Ample.LineBundles.pullbackSection, Functor.map_comp, Category.assoc]

theorem pullbackSection_congr {X Y : Scheme.{u}} {f g : X ⟶ Y} (h : f = g)
    (M : Y.Modules) (s : AbelianModuli.HilbertConstruction.Line.Bundles.structureModule Y ⟶ M) :
    AbelianModuli.HilbertConstruction.Ample.LineBundles.pullbackSection f s ≫ (Scheme.Modules.pullbackCongr h).hom.app M = AbelianModuli.HilbertConstruction.Ample.LineBundles.pullbackSection g s := by
  subst g
  simp [Scheme.Modules.pullbackCongr]

theorem pullbackSection_square {X Y X' Y' : Scheme.{u}}
    (i : Y ⟶ X) (p : X' ⟶ X) (q : Y' ⟶ Y) (j : Y' ⟶ X')
    (h : q ≫ i = j ≫ p) (M : X.Modules) (s : AbelianModuli.HilbertConstruction.Line.Bundles.structureModule X ⟶ M) :
    AbelianModuli.HilbertConstruction.Ample.LineBundles.pullbackSection q (AbelianModuli.HilbertConstruction.Ample.LineBundles.pullbackSection i s) ≫ (Quotients.FiniteDescent.PullbackSectionCongr.Construction.PullbackSectionSquare.iso i p q j h M).hom =
      AbelianModuli.HilbertConstruction.Ample.LineBundles.pullbackSection j (AbelianModuli.HilbertConstruction.Ample.LineBundles.pullbackSection p s) := by
  apply (AbelianModuli.HilbertConstruction.Global.Sections.moduleSectionHomEquiv ((Scheme.Modules.pullback j).obj ((Scheme.Modules.pullback p).obj M))).injective
  change (Quotients.FiniteDescent.PullbackSectionCongr.Construction.PullbackSectionSquare.iso i p q j h M).hom.app ⊤
    (AbelianModuli.HilbertConstruction.Global.Sections.moduleSectionHomEquiv ((Scheme.Modules.pullback q).obj ((Scheme.Modules.pullback i).obj M))
      (AbelianModuli.HilbertConstruction.Ample.LineBundles.pullbackSection q (AbelianModuli.HilbertConstruction.Ample.LineBundles.pullbackSection i s))) = _
  rw [GlobalSectionHomPullback.Construction.moduleSectionHomEquiv_pullback, GlobalSectionHomPullback.Construction.moduleSectionHomEquiv_pullback,
    GlobalSectionHomPullback.Construction.moduleSectionHomEquiv_pullback, GlobalSectionHomPullback.Construction.moduleSectionHomEquiv_pullback]
  exact Quotients.FiniteDescent.PullbackSectionCongr.Construction.PullbackSectionSquare.apply i p q j h M ⊤ ⊤ ⊤ ⊤
    (by simp) (by simp) (by simp) (by simp) (AbelianModuli.HilbertConstruction.Global.Sections.moduleSectionHomEquiv M s)

end Construction

end

end OAI.AlgebraicGeometry.FormalGeometry.Completion.PullbackStructureComparison

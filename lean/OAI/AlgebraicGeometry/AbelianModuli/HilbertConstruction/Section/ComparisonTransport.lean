import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Relative.CoordinateSectionRecovery

/-! # Comparison Transport -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Section.ComparisonTransport

noncomputable section

/-! Isomorphism and pullback transport lemmas used by section comparison. -/
open _root_.CategoryTheory _root_.AlgebraicGeometry
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
def sectionComparisonMap
    {C : Type*} [Category C] {U V M N : C}
    (es : U ≅ M) (et : V ≅ N) (e : U ≅ V) : M ⟶ N :=
  es.inv ≫ e.hom ≫ et.hom

def sectionComparisonIso
    {C : Type*} [Category C] {U V M N : C}
    (es : U ≅ M) (et : V ≅ N) (e : U ≅ V) : M ≅ N where
  hom := sectionComparisonMap es et e
  inv := et.inv ≫ e.inv ≫ es.hom
  hom_inv_id := by simp [sectionComparisonMap]
  inv_hom_id := by simp [sectionComparisonMap]

theorem sectionComparisonIso_hom
    {C : Type*} [Category C] {U V M N : C}
    (es : U ≅ M) (et : V ≅ N) (e : U ≅ V) :
    (sectionComparisonIso es et e).hom = sectionComparisonMap es et e := rfl

theorem sectionIsoComparison
    {C : Type*} [Category C] {W U V M N : C}
    (a : W ⟶ U) (b : W ⟶ V) (s : W ⟶ M) (t : W ⟶ N)
    (es : U ≅ M) (et : V ≅ N) (e : U ≅ V)
    (ha : a ≫ es.hom = s) (hb : b ≫ et.hom = t) (he : a ≫ e.hom = b) :
    s ≫ sectionComparisonMap es et e = t := by
  unfold sectionComparisonMap
  rw [← ha, ← hb]
  simp only [Category.assoc, Iso.hom_inv_id_assoc]
  exact (Category.assoc _ _ _).symm.trans (congrArg (fun k => k ≫ et.hom) he)

theorem pullbackSection_equality_isoApp
    {X Y : Scheme.{u}} {f g : X ⟶ Y} (h : f = g)
    {M : Y.Modules} (q : Line.Bundles.structureModule Y ⟶ M) :
    Ample.LineBundles.pullbackSection f q ≫ ((Scheme.Modules.pullbackCongr h).app M).hom =
      Ample.LineBundles.pullbackSection g q :=
  Global.SectionPullbackComposition.pullbackSection_equality h q

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Section.ComparisonTransport

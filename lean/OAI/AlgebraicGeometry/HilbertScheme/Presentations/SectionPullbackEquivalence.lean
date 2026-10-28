import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Module.PullbackEquivalence
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Ample.LineBundles

/-! # Section Pullback Equivalence -/

namespace OAI.AlgebraicGeometry.HilbertScheme.Presentations.SectionPullbackEquivalence

noncomputable section

/-! Pullback along an actual scheme isomorphism gives a bijection of
module sections, with the canonical structure-sheaf source frame. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

open OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Ample.LineBundles

universe u
variable {X Y : Scheme.{u}}

def sectionPullbackEquivalence (e : X ≅ Y) (M : Y.Modules) :
    (AbelianModuli.HilbertConstruction.Line.Bundles.structureModule Y ⟶ M) ≃ (AbelianModuli.HilbertConstruction.Line.Bundles.structureModule X ⟶ (Scheme.Modules.pullback e.hom).obj M) :=
  (Module.PullbackEquivalence.modulePullbackEquivalence e).fullyFaithfulFunctor.homEquiv.trans
    (Iso.homCongr (AbelianModuli.HilbertConstruction.Line.Bundles.structureModulePullbackIso e.hom) (Iso.refl _))

theorem sectionPullbackEquivalence_apply (e : X ≅ Y) (M : Y.Modules) (s : AbelianModuli.HilbertConstruction.Line.Bundles.structureModule Y ⟶ M) :
    sectionPullbackEquivalence e M s = AbelianModuli.HilbertConstruction.Ample.LineBundles.pullbackSection e.hom s := by
  change (AbelianModuli.HilbertConstruction.Line.Bundles.structureModulePullbackIso e.hom).inv ≫ (Scheme.Modules.pullback e.hom).map s ≫ 𝟙 _ = _
  rw [Category.comp_id]
  rfl

theorem sectionPullback_bijective (e : X ≅ Y) (M : Y.Modules) :
    Function.Bijective (AbelianModuli.HilbertConstruction.Ample.LineBundles.pullbackSection e.hom : (AbelianModuli.HilbertConstruction.Line.Bundles.structureModule Y ⟶ M) → _) := by
  have h : (AbelianModuli.HilbertConstruction.Ample.LineBundles.pullbackSection e.hom : (AbelianModuli.HilbertConstruction.Line.Bundles.structureModule Y ⟶ M) → _) = sectionPullbackEquivalence e M :=
    funext (fun s => (sectionPullbackEquivalence_apply e M s).symm)
  rw [h]
  exact (sectionPullbackEquivalence e M).bijective

end

end OAI.AlgebraicGeometry.HilbertScheme.Presentations.SectionPullbackEquivalence

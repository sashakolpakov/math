import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Proper.SmoothOpenClassification
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.SmoothHilbert.ClassifierNaturality

/-! # Family Smooth Open -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction

noncomputable section

/-! Every relative projective Hilbert family has an actual open base exactly classifying its smooth pullbacks. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

variable {S : Scheme.{u}} {n : ℕ} {P : Polynomial ℚ} (F : RelativeProjective.Families.RelativeProjectiveHilbertFamily S n P)

def RelativeProjective.Families.RelativeProjectiveHilbertFamily.smoothBaseOpen : S.Opens := by
  have : IsProper F.family.scheme.hom := F.family.proper
  have : LocallyOfFinitePresentation F.family.scheme.hom := F.family.locallyFinitePresentation
  exact Proper.SmoothBaseOpen.properSmoothBaseOpen F.family.scheme.hom

theorem RelativeProjective.Families.RelativeProjectiveHilbertFamily.pullback_smooth_iff_range {T : Scheme.{u}} (c : T ⟶ S) :
    Smooth (F.pullback c).family.scheme.hom ↔ Set.range c ⊆ F.smoothBaseOpen := by
  have : IsProper F.family.scheme.hom := F.family.proper
  have : Flat F.family.scheme.hom := F.family.flat
  have : LocallyOfFinitePresentation F.family.scheme.hom := F.family.locallyFinitePresentation
  exact Proper.SmoothOpenClassification.smooth_recovery_iff_range_subset_properSmoothBaseOpen _ _ F.family.scheme.hom c
    (ClosedFamily.Transport.closedFamilyTransport_isPullback (RelativeProjective.BaseMaps.relativeProjectiveBaseMap c n) c
      (RelativeProjective.BaseMaps.relativeProjectiveBaseMap_isPullback c n) F.family.ideal)

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction

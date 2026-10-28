import OAI.AlgebraicGeometry.PELModuli.IntegralModel.AmpleOverSeparatedBase
import OAI.AlgebraicGeometry.Quotients.FiniteDescent.ProjectiveChowModification

/-! # Chow Ample Line -/

namespace OAI.AlgebraicGeometry.PELModuli.IntegralModel.ChowAmpleLine

noncomputable section

/-! The constructed Chow modification carries an actual line bundle
ample over both its original base and its proper target. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

universe u

variable {R : Type u} [CommRing R] {X : Scheme.{u}}
    {f : X ⟶ Spec (.of R)} (D : Quotients.FiniteDescent.ChowModificationModel.Construction.ChowModification.Model f)

def chowAmpleLine : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle D.scheme := D.sectionCover.lineBundle

theorem chowAmpleLine_isAmple [IsProper f] : (chowAmpleLine D).IsAmple := by
  have : IsProper D.projection := D.proper
  have : CompactSpace D.scheme :=
    QuasiCompact.compactSpace_of_compactSpace (D.projection ≫ f)
  refine ⟨isCompact_univ, fun x => ?_⟩
  obtain ⟨i, hi⟩ := D.sectionCover.covers x
  exact ⟨1, Nat.zero_lt_one, chowAmpleLine D, AbelianModuli.HilbertConstruction.Tensor.Powers.isTensorPower_one _,
    D.sectionCover.sectionHom i, hi, D.sectionCover.affine i⟩

theorem chowAmpleLine_relative_to_target [IsProper f] :
    (chowAmpleLine D).IsRelativelyAmple D.projection := by
  have : X.IsSeparated := ⟨by rw [← terminal.comp_from f]; infer_instance⟩
  exact AmpleOverSeparatedBase.ample_isRelativelyAmple_over_separated D.projection (chowAmpleLine_isAmple D)

theorem chowAmpleLine_relative_to_base [IsProper f] :
    (chowAmpleLine D).IsRelativelyAmple (D.projection ≫ f) :=
  AmpleOverSeparatedBase.ample_isRelativelyAmple_over_separated (D.projection ≫ f) (chowAmpleLine_isAmple D)

end

end OAI.AlgebraicGeometry.PELModuli.IntegralModel.ChowAmpleLine

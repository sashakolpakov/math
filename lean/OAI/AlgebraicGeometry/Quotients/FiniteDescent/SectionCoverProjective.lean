import OAI.AlgebraicGeometry.Quotients.FiniteDescent.AffineSectionOf
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Ample.ProjectivePresentation

/-! # Section Cover Projective -/

namespace OAI.AlgebraicGeometry.Quotients.FiniteDescent

noncomputable section

/-! A finite affine section cover on a proper scheme gives a projective presentation. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

universe u

theorem AffineSectionOf.Construction.AffineSectionCover.Data.isAmple {X : Scheme.{u}} [CompactSpace X] (D : AffineSectionOf.Construction.AffineSectionCover.Data X) :
    D.lineBundle.IsAmple := by
  refine ⟨isCompact_univ, fun x => ?_⟩
  obtain ⟨i, hi⟩ := D.covers x
  exact ⟨1, Nat.zero_lt_one, D.lineBundle, AbelianModuli.HilbertConstruction.Tensor.Powers.isTensorPower_one _,
    D.sectionHom i, hi, D.affine i⟩

def AffineSectionOf.Construction.AffineSectionCover.Data.projectivePresentation {S X : Scheme.{u}} [IsAffine S]
    (D : AffineSectionOf.Construction.AffineSectionCover.Data X) (f : X ⟶ S) [IsProper f] : AbelianModuli.HilbertConstruction.Projective.ProjectivePresentations.ProjectivePresentation (Over.mk f) := by
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace f
  exact D.isAmple.projectivePresentation f

end

end OAI.AlgebraicGeometry.Quotients.FiniteDescent

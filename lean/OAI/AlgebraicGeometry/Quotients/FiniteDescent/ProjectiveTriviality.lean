import OAI.AlgebraicGeometry.Quotients.FiniteDescent.ProjectiveSection
import OAI.AlgebraicGeometry.Quotients.FiniteDescent.SectionPair

/-! # Projective Triviality -/

namespace OAI.AlgebraicGeometry.Quotients.FiniteDescent.ProjectiveTriviality

noncomputable section

/-! The trivial-fiber locus of a line bundle in an integral proper
flat projective family is closed. -/

set_option backward.isDefEq.respectTransparency false

open _root_.AlgebraicGeometry _root_.CategoryTheory

universe u

namespace Construction.ProjectiveTrivialityClosed

variable {X S : Scheme.{u}} (π : X ⟶ S) (L : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle X)

def locus : Set S :=
  {x | Nonempty ((L.pullback (π.fiberι x)).sheaf ≅ AbelianModuli.HilbertConstruction.Line.Bundles.structureModule (π.fiber x))}

def fiberEvaluation (x : S) :
    ((L.pullback (π.fiberι x)).tensor ((DualLine.Construction.DualLineBundle.dual L).pullback (π.fiberι x))).sheaf ≅
      AbelianModuli.HilbertConstruction.Line.Bundles.structureModule (π.fiber x) :=
  (PicardPullbackId.Construction.PicardPullback.tensorIso (π.fiberι x) L (DualLine.Construction.DualLineBundle.dual L)).symm ≪≫
    (Scheme.Modules.pullback (π.fiberι x)).mapIso (DualEvaluationIs.Construction.DualEvaluation.iso L) ≪≫
      AbelianModuli.HilbertConstruction.Line.Bundles.structureModulePullbackIso (π.fiberι x)

theorem locus_eq [IsProper π] (hI : ∀ x, IsIntegral (π.fiber x)) :
    locus π L = FiberSection.Construction.FiberSectionSupport.locus π L.sheaf ∩
      FiberSection.Construction.FiberSectionSupport.locus π (DualLine.Construction.DualLineBundle.dual L).sheaf := by
  ext x
  have := hI x
  have : IsIntegral (Over.mk (π.fiberToSpecResidueField x)).left := hI x
  have : IsProper (Over.mk (π.fiberToSpecResidueField x)).hom :=
    inferInstanceAs (IsProper (CategoryTheory.Limits.pullback.snd π (S.fromSpecResidueField x)))
  exact SectionPair.Construction.SectionPairTriviality.pair_iff (Over.mk (π.fiberToSpecResidueField x))
    (L.pullback (π.fiberι x)) ((DualLine.Construction.DualLineBundle.dual L).pullback (π.fiberι x))
    (fiberEvaluation π L x)

theorem isClosed [IsAffine S] [IsNoetherianRing Γ(S, ⊤)] [IsProper π] [Flat π]
    (P : AbelianModuli.HilbertConstruction.Projective.ProjectivePresentations.ProjectivePresentation (Over.mk π)) (hI : ∀ x, IsIntegral (π.fiber x)) :
    IsClosed (locus π L) := by
  rw [locus_eq π L hI]
  have : Flat (Over.mk π).hom := inferInstanceAs (Flat π)
  exact (ProjectiveSection.Construction.ProjectiveSectionSupport.isClosed (Over.mk π) P L).inter
    (ProjectiveSection.Construction.ProjectiveSectionSupport.isClosed (Over.mk π) P (DualLine.Construction.DualLineBundle.dual L))

end Construction.ProjectiveTrivialityClosed

end

end OAI.AlgebraicGeometry.Quotients.FiniteDescent.ProjectiveTriviality

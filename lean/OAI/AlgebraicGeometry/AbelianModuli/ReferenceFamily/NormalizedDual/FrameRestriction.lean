import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Normalized.OpenFrameCriterion
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.NormalizedDual.OpenFrames

/-! # Frame Restriction -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily

noncomputable section

/-! Normalized affine frames restrict to any smaller affine family
open while retaining the original prescribed reduced frame exactly. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory

variable (X : Over Foundations.Scheme.ProjectiveSpace.complexBase) (L : HilbertConstruction.Line.Bundles.LineBundle (LieRanks.dualNumberTest ℂ ⊗ X).left)
    (e₀ : (Scheme.Modules.pullback (RepresentationTheory.Theta.Geometric.Dual.BaseChangeReduction.dualBaseChangeReduction X).left).obj L.sheaf ≅
      ArithmeticGeometry.OrdinaryLocus.Openness.LineBundle.Construction.structureSheafModule X.left)

def Dual.NormalizedFrameCover.NormalizedDualFrame.restrict (a : Dual.NormalizedFrameCover.NormalizedDualFrame X L e₀)
    (U : (LieRanks.dualNumberTest ℂ ⊗ X).left.Opens) (hU : IsAffineOpen U) (h : U ≤ a.domain) :
    Dual.NormalizedFrameCover.NormalizedDualFrame X L e₀ where
  domain := U
  affine := hU
  frame := (Scheme.Modules.restrictFunctorIsoPullback U.ι).symm.app L.sheaf ≪≫
    SheafCohomology.Projective.OpenFrames.Scheme.Modules.restrictOpenTrivialization h (a.localFrame X L e₀).frame
  reduces := Normalized.OpenFrameCriterion.reducedOpenFrame_of_open (RepresentationTheory.Theta.Geometric.Dual.BaseChangeReduction.dualBaseChangeReduction X).left e₀ U
    (SheafCohomology.Projective.OpenFrames.Scheme.Modules.restrictOpenTrivialization h (a.localFrame X L e₀).frame)
    (NormalizedDual.OpenFrames.normalizedDualFrame_open_restrict X L e₀ a U h)

theorem Dual.NormalizedFrameCover.NormalizedDualFrame.restrict_localFrame (a : Dual.NormalizedFrameCover.NormalizedDualFrame X L e₀)
    (U : (LieRanks.dualNumberTest ℂ ⊗ X).left.Opens) (hU : IsAffineOpen U) (h : U ≤ a.domain) :
    (a.restrict X L e₀ U hU h).localFrame X L e₀ =
      ⟨U, SheafCohomology.Projective.OpenFrames.Scheme.Modules.restrictOpenTrivialization h (a.localFrame X L e₀).frame⟩ :=
  congrArg (fun e => (⟨U, e⟩ : LineFrameAtlas.LocalLineFrame L.sheaf)) (Iso.self_symm_id_assoc _ _)

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily

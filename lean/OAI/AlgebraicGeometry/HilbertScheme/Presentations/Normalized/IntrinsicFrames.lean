import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Intrinsic.FrameRestriction
import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Projective.NormalizedTransitions

/-! # Intrinsic Frames -/

namespace OAI.AlgebraicGeometry.HilbertScheme.Presentations.Normalized.IntrinsicFrames

noncomputable section

/-! The normalized line-bundle frames have the same pure-power
transition functions in the native restriction convention used for twists. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.MvPolynomial

universe u
variable (K : Type u) [Field K] {n : ℕ}
variable (L : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle (Proj (Hilbert.Polynomial.GradedHilbert.grading K n)))

def projectiveNormalizedNativeFrame (i : Fin (n + 1)) :
    L.sheaf.restrict (Proj.basicOpen (Hilbert.Polynomial.GradedHilbert.grading K n) (X i)).ι ≅
      AbelianModuli.HilbertConstruction.Line.Bundles.structureModule (Proj.basicOpen (Hilbert.Polynomial.GradedHilbert.grading K n) (X i)).toScheme :=
  Intrinsic.FrameRestriction.nativeOpenFrame _ (Projective.NormalizedFrames.projectiveNormalizedOpenFrame K L i)

theorem projectiveNormalizedNativeFrame_transition (i j : Fin (n + 1)) :
    (Projective.OverlapSectionUnits.projectiveDoubleOpen K i j).topIso.hom
      (FrameTransitionCocycles.frameTransitionValue
        (SheafCohomology.Projective.OpenFrames.Scheme.Modules.restrictOpenTrivialization ((Projective.OverlapSectionUnits.projectiveDoubleOpen_eq_inf K i j).le.trans inf_le_left)
          (projectiveNormalizedNativeFrame K L i))
        (SheafCohomology.Projective.OpenFrames.Scheme.Modules.restrictOpenTrivialization ((Projective.OverlapSectionUnits.projectiveDoubleOpen_eq_inf K i j).le.trans inf_le_right)
          (projectiveNormalizedNativeFrame K L j))) =
      ((Projective.OverlapRatioUnits.projectiveOverlapRatioUnit K i j ^ Projective.LineCommonExponent.projectiveLineCommonExponent K L :
        Γ(Proj (Hilbert.Polynomial.GradedHilbert.grading K n), Projective.OverlapSectionUnits.projectiveDoubleOpen K i j)ˣ) :
          Γ(Proj (Hilbert.Polynomial.GradedHilbert.grading K n), Projective.OverlapSectionUnits.projectiveDoubleOpen K i j)) := by
  have hl : SheafCohomology.Projective.OpenFrames.Scheme.Modules.restrictOpenTrivialization
      ((Projective.OverlapSectionUnits.projectiveDoubleOpen_eq_inf K i j).le.trans inf_le_left) (projectiveNormalizedNativeFrame K L i) =
        Intrinsic.FrameRestriction.nativeOpenFrame (Projective.OverlapSectionUnits.projectiveDoubleOpen K i j) (Projective.NormalizedTransitions.projectiveNormalizedOverlapLeftFrame K L i j) :=
    Intrinsic.FrameRestriction.nativeOpenFrame_restrict _ (Projective.NormalizedFrames.projectiveNormalizedOpenFrame K L i)
  have hr : SheafCohomology.Projective.OpenFrames.Scheme.Modules.restrictOpenTrivialization
      ((Projective.OverlapSectionUnits.projectiveDoubleOpen_eq_inf K i j).le.trans inf_le_right) (projectiveNormalizedNativeFrame K L j) =
        Intrinsic.FrameRestriction.nativeOpenFrame (Projective.OverlapSectionUnits.projectiveDoubleOpen K i j) (Projective.NormalizedTransitions.projectiveNormalizedOverlapRightFrame K L i j) :=
    Intrinsic.FrameRestriction.nativeOpenFrame_restrict _ (Projective.NormalizedFrames.projectiveNormalizedOpenFrame K L j)
  have ht := (congrArg₂ FrameTransitionCocycles.frameTransitionValue hl hr).trans
    (Intrinsic.FrameRestriction.nativeOpenFrame_transition (Projective.OverlapSectionUnits.projectiveDoubleOpen K i j)
      (Projective.NormalizedTransitions.projectiveNormalizedOverlapLeftFrame K L i j) (Projective.NormalizedTransitions.projectiveNormalizedOverlapRightFrame K L i j))
  exact (congrArg (Projective.OverlapSectionUnits.projectiveDoubleOpen K i j).topIso.hom ht).trans
    (Projective.NormalizedTransitions.projectiveNormalizedTransitionValue_eq_power K L i j)

end

end OAI.AlgebraicGeometry.HilbertScheme.Presentations.Normalized.IntrinsicFrames

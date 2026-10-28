import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.AffineProjective.IdealFamilies
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Generated.PullbackAffineCharts
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.RelativeProjective.Pullbacks

/-! # Parameter Closed Families -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Generated.ParameterClosedFamilies

noncomputable section

/-! Every parameter map gives an actual flat closed family in the test scheme's own relative projective space, with exact affine embedded recovery. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

variable {S T : Scheme.{u}} {n B N : ℕ} {r : ℕ → ℕ}
variable (g : T ⟶ (Truncated.GeneratedParameters.truncatedGeneratedParameters S n B r N).left)

def generatedParameterIdealData : AffineProjective.IdealMatching.AffineProjectiveIdealData T n :=
  ((Truncated.UniversalIdeal.truncatedUniversalIdealData S n B r).precomp (Truncated.GeneratedParameters.truncatedGeneratedInclusion S n B r N).left).precomp g

def generatedParameterClosedFamily (hB : Truncated.FinitePersistence.truncatedFlatnessBound n N ≤ B) :
    Closed.Families.FlatClosedFamily (Projective.ProjectivePresentations.projectiveSpaceOver T n) :=
  (generatedParameterIdealData g).flatClosedFamily
    (fun i => (Truncated.AffineUniversalData.truncatedAffineUniversalData
      ((T.affineOpenCover.f i ≫ g) ≫ (Truncated.GeneratedParameters.truncatedGeneratedInclusion S n B r N).left)).generatedFlatClosedFamily
        N hB (Truncated.GeneratedFamily.truncatedGeneratedAffineData_condition (T.affineOpenCover.f i ≫ g)) |>.flat)
    (fun i => (Truncated.AffineUniversalData.truncatedAffineUniversalData
      ((T.affineOpenCover.f i ≫ g) ≫ (Truncated.GeneratedParameters.truncatedGeneratedInclusion S n B r N).left)).generatedFlatClosedFamily
        N hB (Truncated.GeneratedFamily.truncatedGeneratedAffineData_condition (T.affineOpenCover.f i ≫ g)) |>.locallyFinitePresentation)

theorem generatedParameterClosedFamily_affine {R : CommRingCat.{u}}
    (hB : Truncated.FinitePersistence.truncatedFlatnessBound n N ≤ B) (x : Spec R ⟶ T) :
    (generatedParameterClosedFamily g hB).affineProjectivePullback x =
      PullbackAffineCharts.generatedPullbackFamilyAtAffinePoint (x ≫ g) hB := by
  apply Closed.Families.FlatClosedFamily.ext
  exact ((generatedParameterIdealData g).glue_comap x).trans
    (PullbackAffineCharts.generatedPullbackFlatFamily_affine_ideal (x ≫ g) hB).symm

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Generated.ParameterClosedFamilies

import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Stable.BalancedFrameIndex
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Balanced.DeterminantProjectivity
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Balanced.FrameChartCoordinates
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Noetherian.ProjectiveOpen

/-! # Balanced Projective Open -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Stable.BalancedProjectiveOpen

noncomputable section

/-! The stable balanced charts form an actual open subscheme of the
balanced projective scheme. Over a Noetherian coefficient ring this
open has a quasi-projective presentation. -/
open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped Classical
universe u
variable (R : Type u) [CommRing R] {r m : ℕ} (i : Fin m)

def stableBalancedFrameOpen (j : BalancedFrameIndex.StableBalancedFrameIndex.{u} r m) :
    (Proj (Balanced.DeterminantGrading.balancedDeterminantGrading R r m i)).Opens :=
  Proj.basicOpen (Balanced.DeterminantGrading.balancedDeterminantGrading R r m i)
    (Balanced.FrameCoordinatePolynomials.balancedDeterminantMonomialElement R j.exponent j.balanced)

def stableBalancedProjectiveOpen : (Proj (Balanced.DeterminantGrading.balancedDeterminantGrading R r m i)).Opens :=
  ⨆ j : BalancedFrameIndex.StableBalancedFrameIndex.{u} r m, stableBalancedFrameOpen R i j

def stableBalancedQuotientScheme : Over (Spec (.of R)) :=
  Over.mk ((stableBalancedProjectiveOpen R (r := r) i).ι ≫
    HilbertScheme.Presentations.Projective.Flatness.GradedHilbert.projectiveStructureMap (Balanced.DeterminantGrading.balancedDeterminantGrading R r m i))

def stableBalancedFrameOpenIsoSpec (j : BalancedFrameIndex.StableBalancedFrameIndex.{u} r m) :
    (stableBalancedFrameOpen R i j).toScheme ≅
      Spec (.of (Balanced.FrameChartCoordinates.balancedDeterminantChartRing R i j.exponent j.balanced)) :=
  Proj.basicOpenIsoSpec (Balanced.DeterminantGrading.balancedDeterminantGrading R r m i)
    (Balanced.FrameCoordinatePolynomials.balancedDeterminantMonomialElement R j.exponent j.balanced)
    (Balanced.FrameCoordinatePolynomials.balancedDeterminantMonomialElement_mem_grading R j.exponent j.balanced i)
    (j.degree_positive i)

theorem stableBalancedQuotientScheme_quasiProjective [IsNoetherianRing R] (hr : 0 < r) :
    Nonempty (Projective.ProjectivePresentations.QuasiProjectivePresentation (stableBalancedQuotientScheme R (r := r) i)) := by
  obtain ⟨P⟩ := Balanced.DeterminantProjectivity.balancedDeterminant_projective_presentation R hr i
  exact ⟨P.openQuasiProjective (stableBalancedProjectiveOpen R (r := r) i)⟩

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Stable.BalancedProjectiveOpen

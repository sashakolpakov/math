import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.EmptyProjectiveFamilies
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.EmptyProjectiveParameters
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Hilbert.RankObstructions

/-! # Empty Points -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.EmptyPoints

noncomputable section

/-! In the numerically impossible case, maps to the actual empty parameter scheme classify Hilbert families over arbitrary test schemes. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

variable {S : Scheme.{u}} {T : Over S} {n N : ℕ} {P : Polynomial ℚ}
variable (hN : HilbertScheme.Presentations.Uniform.FamilyCoordinates.GradedHilbert.uniformHilbertFamilyDegree.{u} n P ≤ N) (hbad : ¬ Generated.RankTests.GeneratedHilbertRankTest n P N)

def relativeHilbertEmptyParameterEquiv :
    RelativeProjective.Families.RelativeProjectiveHilbertFamily T.left n P ≃ (T ⟶ EmptyProjectiveParameters.emptyProjectiveParameter S) where
  toFun F := by
    letI := F.isEmpty_of_failedRankTest hN hbad
    exact EmptyProjectiveParameters.overEmptySourceMap T (EmptyProjectiveParameters.emptyProjectiveParameter S)
  invFun g := by
    letI : IsEmpty T.left := g.left.base.hom.1.isEmpty
    exact EmptyProjectiveFamilies.emptyRelativeProjectiveHilbertFamily n P
  left_inv F := by
    let := F.isEmpty_of_failedRankTest hN hbad
    exact Subsingleton.elim _ _
  right_inv g := by
    let : IsEmpty T.left := g.left.base.hom.1.isEmpty
    exact EmptyProjectiveParameters.overEmptySourceMap_unique _ _

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.EmptyPoints

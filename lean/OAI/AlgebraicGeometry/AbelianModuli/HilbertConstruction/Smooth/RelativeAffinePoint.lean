import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.SmoothHilbert.AffineUniqueness
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Smooth.ClosedFamilyPullbacks

/-! # Relative Affine Point -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction

noncomputable section

/-! Chosen affine parameter points of smooth relative Hilbert families, with exact recovery of the embedded affine family. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

variable {S : Scheme.{u}} {T : Over S} {n B N : ℕ} {P : Polynomial ℚ}
variable (F : RelativeProjective.Families.RelativeProjectiveHilbertFamily T.left n P) [Smooth F.family.scheme.hom]
variable (hN : HilbertScheme.Presentations.Uniform.FamilyCoordinates.GradedHilbert.uniformHilbertFamilyDegree.{u} n P ≤ N) (hflat : Truncated.FinitePersistence.truncatedFlatnessBound n N ≤ B)

def RelativeProjective.Families.RelativeProjectiveHilbertFamily.smoothAffinePoint {R : CommRingCat.{u}} (x : Spec R ⟶ T.left) :
    Over.mk (x ≫ T.hom) ⟶ Truncated.GeneratedParameters.truncatedGeneratedParameters S n B (Uniform.GeneratedCoordinates.generatedHilbertRanks n P N) N := by
  have : Smooth (F.affineFamily x).val.scheme.hom := F.affineFamily_smooth x
  exact (SmoothHilbert.AffineExistence.smoothHilbertAffinePoint_exists (F.affineFamily x) hN hflat (x ≫ T.hom)).choose

theorem RelativeProjective.Families.RelativeProjectiveHilbertFamily.smoothAffinePoint_pullback {R : CommRingCat.{u}} (x : Spec R ⟶ T.left) :
    Generated.PullbackAffineCharts.generatedPullbackFamilyAtAffinePoint (F.smoothAffinePoint hN hflat x).left hflat = (F.affineFamily x).val := by
  have : Smooth (F.affineFamily x).val.scheme.hom := F.affineFamily_smooth x
  exact (SmoothHilbert.AffineExistence.smoothHilbertAffinePoint_exists (F.affineFamily x) hN hflat (x ≫ T.hom)).choose_spec

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction

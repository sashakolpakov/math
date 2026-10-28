import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.SmoothHilbert.DataUniqueness
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Generated.AffinePointIdeal
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.SmoothHilbert.AffineExistence

/-! # Affine Uniqueness -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.SmoothHilbert.AffineUniqueness

noncomputable section

/-! The actual affine parameter point of a smooth Hilbert family is unique over every coefficient ring. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

variable {R : CommRingCat.{u}} {S : Scheme.{u}} {n B N : ℕ} {P : Polynomial ℚ}
variable (F : Flat.ClosedFamilies.FlatClosedHilbertFamily R n P) [Smooth F.val.scheme.hom]
variable (hN : HilbertScheme.Presentations.Uniform.FamilyCoordinates.GradedHilbert.uniformHilbertFamilyDegree.{u} n P ≤ N)
variable (hflat : Truncated.FinitePersistence.truncatedFlatnessBound n N ≤ B) (f : Spec R ⟶ S)

include hN

theorem smoothHilbertAffinePoint_unique
    (x y : Over.mk f ⟶ Truncated.GeneratedParameters.truncatedGeneratedParameters S n B (Uniform.GeneratedCoordinates.generatedHilbertRanks n P N) N)
    (hx : Generated.PullbackAffineCharts.generatedPullbackFamilyAtAffinePoint x.left hflat = F.val)
    (hy : Generated.PullbackAffineCharts.generatedPullbackFamilyAtAffinePoint y.left hflat = F.val) : x = y := by
  apply (Truncated.GeneratedParameters.truncatedGeneratedAffinePointEquiv R f).symm.injective
  apply F.generatedData_unique hN ((Nat.le_add_right N _).trans hflat)
  · exact (Generated.AffinePointIdeal.generatedAffinePoint_data_projectiveIdeal f x hflat).trans (congrArg Closed.Families.FlatClosedFamily.ideal hx)
  · exact (Generated.AffinePointIdeal.generatedAffinePoint_data_projectiveIdeal f y hflat).trans (congrArg Closed.Families.FlatClosedFamily.ideal hy)

theorem smoothHilbertAffinePoint_existsUnique :
    ∃! x : Over.mk f ⟶ Truncated.GeneratedParameters.truncatedGeneratedParameters S n B (Uniform.GeneratedCoordinates.generatedHilbertRanks n P N) N,
      Generated.PullbackAffineCharts.generatedPullbackFamilyAtAffinePoint x.left hflat = F.val := by
  obtain ⟨x, hx⟩ := AffineExistence.smoothHilbertAffinePoint_exists F hN hflat f
  exact ⟨x, hx, fun y hy => smoothHilbertAffinePoint_unique F hN hflat f y x hy hx⟩

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.SmoothHilbert.AffineUniqueness

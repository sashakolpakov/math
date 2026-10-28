import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Smooth.RelativeUniversality
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Relative.ParameterEquivalence

/-! # Relative Family Recovery -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction

noncomputable section

/-! The global smooth classifier recovers the actual relative Hilbert family, with uniqueness stated as equality of families. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

variable {S : Scheme.{u}} {T : Over S} {n B N : ℕ} {P : Polynomial ℚ}
variable (F : RelativeProjective.Families.RelativeProjectiveHilbertFamily T.left n P) [Smooth F.family.scheme.hom]
variable (hN : HilbertScheme.Presentations.Uniform.FamilyCoordinates.GradedHilbert.uniformHilbertFamilyDegree.{u} n P ≤ N) (hflat : Truncated.FinitePersistence.truncatedFlatnessBound n N ≤ B)
variable (htest : Truncated.PolynomialTest.truncatedHilbertTestBound n N ≤ B) (hr : Generated.RankTests.GeneratedHilbertRankTest n P N)

theorem RelativeProjective.Families.RelativeProjectiveHilbertFamily.smoothClassifyingMap_family :
    Generated.ParameterFamilies.generatedParameterHilbertFamily (F.smoothClassifyingMap hN hflat).left hflat htest hr = F := by
  apply RelativeProjective.Families.RelativeProjectiveHilbertFamily.ext
  apply Closed.Families.FlatClosedFamily.ext
  apply ClosedFamily.OpenEquality.ideal_eq_of_open_cover (Projective.AffineCover.projectiveAffineOpenCover T.left.affineOpenCover n)
  intro i
  let x := T.left.affineOpenCover.f i
  have he := (Generated.ParameterClosedFamilies.generatedParameterClosedFamily_affine (F.smoothClassifyingMap hN hflat).left hflat x).trans
    (F.smoothClassifyingMap_pullback hN hflat x)
  exact congrArg Closed.Families.FlatClosedFamily.ideal he

include hN in
theorem RelativeProjective.Families.RelativeProjectiveHilbertFamily.existsUnique_smoothParameterFamily :
    ∃! g : T ⟶ Truncated.GeneratedParameters.truncatedGeneratedParameters S n B (Uniform.GeneratedCoordinates.generatedHilbertRanks n P N) N,
      Generated.ParameterFamilies.generatedParameterHilbertFamily g.left hflat htest hr = F := by
  refine ⟨F.smoothClassifyingMap hN hflat, F.smoothClassifyingMap_family hN hflat htest hr, ?_⟩
  intro g hg
  apply F.smoothClassifyingMap_unique hN hflat g
  intro R x
  have he := congrArg (fun H : RelativeProjective.Families.RelativeProjectiveHilbertFamily T.left n P =>
    H.family.affineProjectivePullback x) hg
  exact (Generated.ParameterClosedFamilies.generatedParameterClosedFamily_affine g.left hflat x).symm.trans he

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction

import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Generated.ParameterFamilies
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Relative.Universality

/-! # Parameter Equivalence -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction

noncomputable section

/-! The constructed open scheme classifies actual relative projective Hilbert families on locally noetherian tests, with inverse constructions. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

theorem RelativeProjective.Families.RelativeProjectiveHilbertFamily.ext {T : Scheme.{u}} {n : ℕ} {P : Polynomial ℚ}
    {F G : RelativeProjective.Families.RelativeProjectiveHilbertFamily T n P} (h : F.family = G.family) : F = G := by
  cases F
  cases G
  cases h
  rfl

variable {S : Scheme.{u}} {T : Over S} [IsLocallyNoetherian T.left]
variable {n B N : ℕ} {P : Polynomial ℚ}
variable (hN : HilbertScheme.Presentations.Uniform.FamilyCoordinates.GradedHilbert.uniformHilbertFamilyDegree.{u} n P ≤ N)
variable (hflat : Truncated.FinitePersistence.truncatedFlatnessBound n N ≤ B) (htest : Truncated.PolynomialTest.truncatedHilbertTestBound n N ≤ B)
variable (hr : Generated.RankTests.GeneratedHilbertRankTest n P N)

theorem Relative.ParameterEquivalence.generatedParameterHilbertFamily_classifyingMap
    (g : T ⟶ Truncated.GeneratedParameters.truncatedGeneratedParameters S n B (Uniform.GeneratedCoordinates.generatedHilbertRanks n P N) N) :
    (Generated.ParameterFamilies.generatedParameterHilbertFamily g.left hflat htest hr).classifyingMap hN hflat htest hr = g := by
  symm
  apply RelativeProjective.Families.RelativeProjectiveHilbertFamily.classifyingMap_unique
  intro R _ x
  exact (Generated.ParameterClosedFamilies.generatedParameterClosedFamily_affine g.left hflat x).symm

theorem Relative.ParameterEquivalence.relativeHilbertFamily_classifyingMap_roundTrip (F : RelativeProjective.Families.RelativeProjectiveHilbertFamily T.left n P) :
    Generated.ParameterFamilies.generatedParameterHilbertFamily (F.classifyingMap hN hflat htest hr).left hflat htest hr = F := by
  apply RelativeProjective.Families.RelativeProjectiveHilbertFamily.ext
  apply Closed.Families.FlatClosedFamily.ext
  apply ClosedFamily.OpenEquality.ideal_eq_of_open_cover (Projective.AffineCover.projectiveAffineOpenCover T.left.affineOpenCover n)
  intro i
  let := Noetherian.AffineGluing.affineCoverCoordinateRing_noetherian T.left i
  let x := T.left.affineOpenCover.f i
  have he := (Generated.ParameterClosedFamilies.generatedParameterClosedFamily_affine (F.classifyingMap hN hflat htest hr).left hflat x).trans
    (F.classifyingMap_pullback hN hflat htest hr x)
  exact congrArg Closed.Families.FlatClosedFamily.ideal he

def Relative.ParameterEquivalence.relativeProjectiveHilbertParameterEquiv : RelativeProjective.Families.RelativeProjectiveHilbertFamily T.left n P ≃
    (T ⟶ Truncated.GeneratedParameters.truncatedGeneratedParameters S n B (Uniform.GeneratedCoordinates.generatedHilbertRanks n P N) N) where
  toFun F := F.classifyingMap hN hflat htest hr
  invFun g := Generated.ParameterFamilies.generatedParameterHilbertFamily g.left hflat htest hr
  left_inv := Relative.ParameterEquivalence.relativeHilbertFamily_classifyingMap_roundTrip hN hflat htest hr
  right_inv := Relative.ParameterEquivalence.generatedParameterHilbertFamily_classifyingMap hN hflat htest hr

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction

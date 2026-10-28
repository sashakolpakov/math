import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Hilbert.RankNecessity
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.RelativeProjective.Families
import Mathlib.AlgebraicGeometry.ResidueField

/-! # Rank Obstructions -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction

noncomputable section

/-! Failure of the numerical Hilbert rank test forces every test scheme carrying such a Hilbert family to be empty. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

variable {T : Scheme.{u}} {n N : ℕ} {P : Polynomial ℚ}
variable (F : RelativeProjective.Families.RelativeProjectiveHilbertFamily T n P) (hN : HilbertScheme.Presentations.Uniform.FamilyCoordinates.GradedHilbert.uniformHilbertFamilyDegree.{u} n P ≤ N)

include F hN

theorem RelativeProjective.Families.RelativeProjectiveHilbertFamily.generatedRankTest_of_fieldPoint (K : Type u) [Field K] (x : Spec (CommRingCat.of K) ⟶ T) :
    Generated.RankTests.GeneratedHilbertRankTest n P N :=
  (F.affineFamily x).saturatedIdeal.generatedRankTest (F.fieldHilbert K x) hN

theorem RelativeProjective.Families.RelativeProjectiveHilbertFamily.generatedRankTest_of_point (x : T) : Generated.RankTests.GeneratedHilbertRankTest n P N :=
  F.generatedRankTest_of_fieldPoint hN (T.residueField x) (T.fromSpecResidueField x)

theorem RelativeProjective.Families.RelativeProjectiveHilbertFamily.isEmpty_of_failedRankTest (h : ¬ Generated.RankTests.GeneratedHilbertRankTest n P N) : IsEmpty T :=
  ⟨fun x => h (F.generatedRankTest_of_point hN x)⟩

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction

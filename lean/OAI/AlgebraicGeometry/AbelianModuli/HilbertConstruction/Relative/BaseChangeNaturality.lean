import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.RelativeProjective.FamilyBaseChange
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Relative.ParameterEquivalence

/-! # Base Change Naturality -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction

noncomputable section

/-! Pullbacks of actual relative Hilbert families satisfy the identity and composition laws, and the locally noetherian classifier commutes with every base map. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

variable {S T U : Scheme.{u}} {n : ℕ} {P : Polynomial ℚ}

theorem RelativeProjective.Families.RelativeProjectiveHilbertFamily.pullback_id (F : RelativeProjective.Families.RelativeProjectiveHilbertFamily S n P) : F.pullback (𝟙 S) = F := by
  apply RelativeProjective.Families.RelativeProjectiveHilbertFamily.ext
  apply Closed.Families.FlatClosedFamily.ext
  change F.family.ideal.comap (RelativeProjective.BaseMaps.relativeProjectiveBaseMap (𝟙 S) n) = F.family.ideal
  rw [RelativeProjective.BaseFunctoriality.relativeProjectiveBaseMap_id, Scheme.IdealSheafData.comap_id]

theorem RelativeProjective.Families.RelativeProjectiveHilbertFamily.pullback_comp (F : RelativeProjective.Families.RelativeProjectiveHilbertFamily S n P) (f : T ⟶ S) (g : U ⟶ T) :
    (F.pullback f).pullback g = F.pullback (g ≫ f) := by
  apply RelativeProjective.Families.RelativeProjectiveHilbertFamily.ext
  apply Closed.Families.FlatClosedFamily.ext
  change (F.family.ideal.comap (RelativeProjective.BaseMaps.relativeProjectiveBaseMap f n)).comap (RelativeProjective.BaseMaps.relativeProjectiveBaseMap g n) =
    F.family.ideal.comap (RelativeProjective.BaseMaps.relativeProjectiveBaseMap (g ≫ f) n)
  rw [RelativeProjective.BaseFunctoriality.relativeProjectiveBaseMap_comp]
  exact (F.family.ideal.comap_comp _ _).symm

variable {V W : Over S} [IsLocallyNoetherian V.left] [IsLocallyNoetherian W.left]
variable {B N : ℕ} (F : RelativeProjective.Families.RelativeProjectiveHilbertFamily V.left n P)
variable (hN : HilbertScheme.Presentations.Uniform.FamilyCoordinates.GradedHilbert.uniformHilbertFamilyDegree.{u} n P ≤ N)
variable (hflat : Truncated.FinitePersistence.truncatedFlatnessBound n N ≤ B) (htest : Truncated.PolynomialTest.truncatedHilbertTestBound n N ≤ B)
variable (hr : Generated.RankTests.GeneratedHilbertRankTest n P N)

theorem RelativeProjective.Families.RelativeProjectiveHilbertFamily.classifyingMap_natural (f : W ⟶ V) :
    (F.pullback f.left).classifyingMap hN hflat htest hr = f ≫ F.classifyingMap hN hflat htest hr := by
  symm
  apply (F.pullback f.left).classifyingMap_unique
  intro R _ x
  change Generated.PullbackAffineCharts.generatedPullbackFamilyAtAffinePoint (x ≫ (f.left ≫ (F.classifyingMap hN hflat htest hr).left)) hflat =
    (F.family.projectiveBaseChange f.left).affineProjectivePullback x
  rw [← Category.assoc]
  exact (F.classifyingMap_pullback hN hflat htest hr (x ≫ f.left)).trans
    (F.family.projectiveBaseChange_affine f.left x).symm

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction

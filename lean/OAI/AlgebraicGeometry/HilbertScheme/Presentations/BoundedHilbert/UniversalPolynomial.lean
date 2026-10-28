import OAI.AlgebraicGeometry.HilbertScheme.Presentations.BoundedHilbert.UniversalIdeal
import OAI.AlgebraicGeometry.HilbertScheme.Presentations.FieldPointOpenLift

/-! # Universal Polynomial -/

namespace OAI.AlgebraicGeometry.HilbertScheme.Presentations.BoundedHilbert.UniversalPolynomial.GradedHilbert

noncomputable section

/-! The global bounded Hilbert universal family satisfies the exact
field-fiber Hilbert-polynomial predicate in the Presentations statement. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

universe u
variable {ι : Type u} [Fintype ι] [DecidableEq ι] (n N : ℕ)
variable (S : Scheme.{u}) [IsLocallyNoetherian S] (q : ℕ → ℕ) (P : Polynomial ℚ)

theorem boundedHilbertUniversalFamily_hasFiberHilbertPolynomial
    (hP : DegreeLocus.GradedHilbert.RankProfileRealizes.{u} n N q P) :
    Has.Core.HasFiberHilbertPolynomial (Intrinsic.ProjectivePresentation.GradedHilbert.canonicalProjectivePresentation S n)
      (UniversalFamily.GradedHilbert.boundedHilbertUniversalFamily (ι := ι) n N S q) P := by
  intro K _ a
  let H := Data.GradedHilbert.boundedHilbertOver (ι := ι) n N S q
  let C := Hilbert.FamilyLocality.testOpenCover (fun p : ι → Homogeneous.CoordinateBasis.GradedHilbert.DegreeIndex.{u} n N => NormalizedHilbert.Chart.GradedHilbert.normalizedHilbertChart p S q)
    (fun p => ChartPullback.GradedHilbert.boundedHilbertChartOverMap p S q) (Data.GradedHilbert.boundedHilbertCharts_cover n N S q)
  obtain ⟨p, b, hb⟩ := FieldPointOpenLift.fieldPoint_lift_openCover C a
  change ι → Homogeneous.CoordinateBasis.GradedHilbert.DegreeIndex.{u} n N at p
  let V := NormalizedHilbert.Chart.GradedHilbert.normalizedHilbertChart p S q
  let M := Normalized.Chart.Grassmannian.normalizedChart p S
  let v : V ⟶ H := ChartPullback.GradedHilbert.boundedHilbertChartOverMap p S q
  let m : V ⟶ M := NormalizedHilbert.Chart.GradedHilbert.normalizedHilbertChartInclusion p S q
  let β : Spec (CommRingCat.of K) ⟶ V.left := b
  have hβ : β ≫ v.left = a := hb
  have hbase : β ≫ V.hom = a ≫ H.hom := by
    rw [← v.w, ← Category.assoc, hβ]
  let t : Over S := Over.mk (a ≫ H.hom)
  let k : t ⟶ V := Over.homMk β hbase
  let z : t ⟶ H := Over.homMk a rfl
  have hk : k ≫ v = z := Over.OverMorphism.ext hβ
  have hideal : (Hilbert.Functor.pullbackFamily (Intrinsic.PolynomialAmbient.GradedHilbert.relativeProjectiveOver S n) z
      (UniversalFamily.GradedHilbert.boundedHilbertUniversalFamily (ι := ι) n N S q)).val =
      (Global.PolynomialInclusion.GradedHilbert.globalPolynomialInclusion M (Normalized.PolynomialKernel.GradedHilbert.normalizedPolynomialIdeal p (Normalized.Chart.Grassmannian.universalNormalizedMatrix p S)) (k ≫ m)).ker := by
    rw [← hk]
    exact UniversalIdeal.GradedHilbert.boundedHilbertUniversalFamily_chart_ideal p S q k
  dsimp only [Intrinsic.ProjectivePresentation.GradedHilbert.canonicalProjectivePresentation]
  rw [hideal]
  let I := Normalized.PolynomialKernel.GradedHilbert.normalizedPolynomialIdeal p (Normalized.Chart.Grassmannian.universalNormalizedMatrix p S)
  let γ : Spec (CommRingCat.of K) ⟶ M.left := β ≫ m.left
  have hγ : γ ≫ M.hom = a ≫ H.hom := (k ≫ m).w
  refine ⟨Global.ProjectivePoint.GradedHilbert.globalProjectiveSchemePointMap M n γ,
    Global.PolynomialPointEmbedding.GradedHilbert.globalPolynomialPointEmbedding M I γ (a ≫ H.hom) hγ, ?_, ?_, ?_, ?_, ?_⟩
  · have hp := Global.ProjectivePoint.GradedHilbert.globalProjectiveSchemePointMap_isPullback M n γ
    rw [hγ] at hp
    exact hp
  · exact Global.PolynomialPointEmbedding.GradedHilbert.globalPolynomialPointEmbedding_isClosedImmersion M I γ (a ≫ H.hom) hγ
  · exact (Global.PolynomialPointEmbedding.GradedHilbert.globalPolynomialPointEmbedding_ambient M I γ (a ≫ H.hom) hγ).trans
      ((Category.comp_id _).symm.trans (Category.assoc _ _ _))
  · exact Global.PolynomialPointEmbedding.GradedHilbert.globalPolynomialPointEmbedding_projection M I γ (a ≫ H.hom) hγ
  · apply Global.PolynomialPointEmbedding.GradedHilbert.globalPolynomialPointEmbedding_hilbertPolynomial M I γ (a ≫ H.hom) hγ P
    exact PointIdeal.GradedHilbert.bounded_hilbert_point_ideal_polynomial M (NormalizedHilbert.Chart.GradedHilbert.universalPolynomialGenerators p S) N
      (NormalizedHilbert.Chart.GradedHilbert.universalPolynomialGenerators_homogeneous p S) q P hP m (NormalizedHilbert.Chart.GradedHilbert.normalizedHilbertChart_universal_mem p S q) β

end

end OAI.AlgebraicGeometry.HilbertScheme.Presentations.BoundedHilbert.UniversalPolynomial.GradedHilbert

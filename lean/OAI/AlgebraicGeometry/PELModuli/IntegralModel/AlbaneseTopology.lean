import OAI.AlgebraicGeometry.PELModuli.IntegralModel.Albanese
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.ComponentUniformization
import OAI.NumberTheory.ArithmeticGroups.Diagonal
import OAI.AlgebraicGeometry.AbelianVariety.AnalyticGroup
import Mathlib.Analysis.Convex.PathConnected

/-! # Albanese Topology -/

namespace OAI.AlgebraicGeometry.PELModuli.IntegralModel.AlbaneseTopology

noncomputable section

/-!
Path connectedness needed by the degree-one product comparison. ReferenceFamily's
explicit ball covers imply connectedness of the actual analytic components;
the surjective Albanese word map then implies it for their Albanese varieties.
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj

namespace BallTopology

variable {E : Type} [Field E] [NumberField E] [Algebra ℚ E]
  [NumberField.IsCMField E] {s : ℕ} (P : AbelianModuli.ReferenceFamily.Datum.RankThreePELDatum E s)

omit [NumberField E] [NumberField.IsCMField E] in
theorem mem_domain_iff (z : Geometry.ComplexBall.PrescribedSignsB.BallChart) :
    z ∈ P.domain ↔
      Complex.normSq (z 0) + Complex.normSq (z 1) + (P.μ P.b).re < 0 := by
  unfold AbelianModuli.ReferenceFamily.Datum.RankThreePELDatum.domain
  rw [Set.mem_ofPred_eq, NumberTheory.ArithmeticGroups.Diagonal.CongruenceLevel.localB_diagonal_real]
  simp [Geometry.ComplexBall.PrescribedSignsB.lineVector, AbelianModuli.ReferenceFamily.Datum.RankThreePELDatum.μ]

omit [NumberField E] [NumberField.IsCMField E] in
theorem domain_starConvex : StarConvex ℝ 0 P.domain := by
  intro z hz a b ha hb hab
  simp only [smul_zero, zero_add]
  rw [mem_domain_iff] at hz ⊢
  simp only [Pi.smul_apply, Complex.real_smul, Complex.normSq_mul, Complex.normSq_ofReal]
  have hb1 : b ≤ 1 := by linarith
  have hsquare : b * b ≤ 1 := by nlinarith
  have hnorm := add_nonneg (Complex.normSq_nonneg (z 0)) (Complex.normSq_nonneg (z 1))
  have hmul := mul_nonneg (sub_nonneg.mpr hsquare) hnorm
  nlinarith

omit [NumberField E] [NumberField.IsCMField E] in
theorem domain_pathConnected (hnegative : (P.μ P.b).re < 0) :
    PathConnectedSpace P.Domain := by
  apply isPathConnected_iff_pathConnectedSpace.mp
  apply (domain_starConvex P).isPathConnected
  rw [mem_domain_iff]
  simpa using hnegative

omit [NumberField E] [NumberField.IsCMField E] in
theorem pathConnected_of_ballCover (hnegative : (P.μ P.b).re < 0)
    (X : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety) (q : P.Domain → X.analyticSpace)
    (hq : P.IsBallCover X q) : PathConnectedSpace X.analyticSpace := by
  let : PathConnectedSpace P.Domain := domain_pathConnected P hnegative
  exact hq.1.pathConnectedSpace hq.2.1.continuous

theorem pathConnected_of_arithmeticBallUniformized
    (hnegative : (P.μ P.b).re < 0) (X : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety) (N : ℕ)
    (h : P.IsArithmeticBallUniformized X N) : PathConnectedSpace X.analyticSpace := by
  obtain ⟨_, _, _, _, _, _, _, _, _, q, hq, _⟩ := h
  exact pathConnected_of_ballCover P hnegative X q hq

end BallTopology

theorem schemeProductPoints_pathConnected (X Y : Over Foundations.Scheme.ProjectiveSpace.complexBase)
    [PathConnectedSpace (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X)] [PathConnectedSpace (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints Y)] :
    PathConnectedSpace (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints (X ⊗ Y)) :=
  (AbelianVariety.AnalyticGroup.Constructions.ExteriorCohomology.schemePointProductHomeomorph X Y).symm.surjective.pathConnectedSpace
    (AbelianVariety.AnalyticGroup.Constructions.ExteriorCohomology.schemePointProductHomeomorph X Y).symm.continuous

theorem wordPoints_pathConnected (X : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation)
    [PathConnectedSpace (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X.toOver)] (n : ℕ) :
    PathConnectedSpace (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints (Albanese.Construction.ImageWords.wordDomain X n)) := by
  induction n with
  | zero =>
    let : Subsingleton (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints (Albanese.Construction.ImageWords.wordDomain X 0)) :=
      inferInstanceAs (Subsingleton (Over.mk (𝟙 Foundations.Scheme.ProjectiveSpace.complexBase) ⟶ 𝟙_ (Over Foundations.Scheme.ProjectiveSpace.complexBase)))
    let : Nonempty (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints (Albanese.Construction.ImageWords.wordDomain X 0)) := ⟨𝟙 _⟩
    infer_instance
  | succ n ih =>
    let : PathConnectedSpace (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints (X.toOver ⊗ X.toOver)) :=
      schemeProductPoints_pathConnected X.toOver X.toOver
    exact schemeProductPoints_pathConnected (Albanese.Construction.ImageWords.wordDomain X n) (X.toOver ⊗ X.toOver)

/-- The generated Albanese is a continuous image of a connected word domain. -/
theorem albanesePoints_pathConnected (X : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
    [PathConnectedSpace X.analyticSpace]
    (x₀ : Over.mk (𝟙 Foundations.Scheme.ProjectiveSpace.complexBase) ⟶ X.toOver)
    (A : ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety) (a : X.toOver ⟶ A.toOver)
    (ha : Albanese.IsAlbaneseMap X.presentation x₀ A a) :
    PathConnectedSpace A.variety.analyticSpace := by
  let n := Foundations.Scheme.TranscendenceDimension.schemeTranscendenceDimension A.variety.structureMap + 1
  let : PathConnectedSpace (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints (Albanese.Construction.ImageWords.wordDomain X.presentation n)) :=
    wordPoints_pathConnected X.presentation n
  exact (Albanese.Construction.GeneratingWords.generating_word_point_surjective X.presentation x₀ A a
    (Albanese.albanese_generates X.presentation x₀ A a ha) n (Nat.le_succ _)).pathConnectedSpace
      (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.continuous_map (Albanese.Construction.ImageWords.wordMap X.presentation A a n))

end

end OAI.AlgebraicGeometry.PELModuli.IntegralModel.AlbaneseTopology

import OAI.RepresentationTheory.Theta.Adelic.GeometricSiegelBranch
import OAI.RepresentationTheory.Theta.Adelic.SymplecticComposition

/-! # Siegel Branch Cocycle -/

namespace OAI.RepresentationTheory.Theta.Adelic.SiegelBranchCocycle

noncomputable section

/-! The entire Siegel branch satisfies the group law: its determinant
square composes by the actual symplectic representation, and uniqueness
continues the already proved geometric cocycle from the ball. -/

open scoped Classical _root_.NumberField _root_.Matrix.Norms.Elementwise

open _root_.Matrix
open OAI.RepresentationTheory.Theta.Adelic.BallGeometryData OAI.RepresentationTheory.Theta.Adelic.BallNatural OAI.RepresentationTheory.Theta.Adelic.RationalSU OAI.RepresentationTheory.Theta.Adelic.GeometricGroup
open OAI.RepresentationTheory.Theta.Adelic.DataTheta OAI.RepresentationTheory.Theta.Adelic.PeriodCoordinates OAI.RepresentationTheory.Theta.Adelic.CoordinateFrameAction.PeriodCovariance OAI.RepresentationTheory.Theta.Adelic.RealSymplecticAction
open OAI.RepresentationTheory.Theta.Adelic.GeometricAutomorphy OAI.RepresentationTheory.Theta.Adelic.GeometricSiegelBranch OAI.RepresentationTheory.Theta.Adelic.SymplecticComposition

theorem denominator_of_one {I : Type} [Fintype I] [DecidableEq I]
    (g : AlgebraicGeometry.ComplexMultiplication.CMSymplecticSiegel.CM.SymplecticBlocks I ℝ) (hg : DataTheta.blockMatrix g = 1) (Z : Matrix I I ℂ) :
    g.complexify.denominator Z = 1 := by
  have hC : g.C = 0 := by
    ext i j
    have h := congrArg (fun M : Matrix (I ⊕ I) (I ⊕ I) ℝ => M (.inr i) (.inl j)) hg
    change g.C i j = (1 : Matrix (I ⊕ I) (I ⊕ I) ℝ) (.inr i) (.inl j) at h
    simpa only [Matrix.one_apply, reduceCtorEq, ite_false, Matrix.zero_apply] using h
  have hD : g.D = 1 := by
    ext i j
    have h := congrArg (fun M : Matrix (I ⊕ I) (I ⊕ I) ℝ => M (.inr i) (.inr j)) hg
    change g.D i j = (1 : Matrix (I ⊕ I) (I ⊕ I) ℝ) (.inr i) (.inr j) at h
    simpa only [Matrix.one_apply, Sum.inr.injEq] using h
  simp [AlgebraicGeometry.ComplexMultiplication.CMSymplecticSiegel.CM.SymplecticBlocks.denominator, AlgebraicGeometry.ComplexMultiplication.CMSymplecticSiegel.CM.SymplecticBlocks.complexify, hC, hD]

variable {F : Type} [Field F] [NumberField F] {d : F} {m : ℕ}
variable {H : (Matrix (Fin 3) (Fin 3) (Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic F d))ˣ}
variable {K : (Matrix (Fin m) (Fin m) (Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic F d))ˣ}
variable (A : BallGeometryData.BallArithmeticData F d m H K) (P : Weil.AdelicSplitting.Assembly.Construction.GlobalFrames F d 3 m H K)

def branchProduct (g h : RationalSU.ArchimedeanSU F H) (M : Matrix (BallGeometryData.FrameIndex A) (BallGeometryData.FrameIndex A) ℂ) : ℂ :=
  GeometricSiegelBranch.geometricSiegelBranch A P g ((RealSymplecticAction.realSymplecticBlocks A P h).complexify.fractional M) *
    GeometricSiegelBranch.geometricSiegelBranch A P h M

theorem branchProduct_continuous (g h : RationalSU.ArchimedeanSU F H) :
    ContinuousOn (branchProduct A P g h) (PoissonAutomorphyNormalizationData.siegelSet (BallGeometryData.FrameIndex A)) := by
  have hg := (GeometricSiegelBranch.geometricSiegelBranch_holomorphic A P g).continuousOn.comp_continuous
    continuous_subtype_val (fun W : PoissonAutomorphyNormalizationData.Domain (BallGeometryData.FrameIndex A) => W.property)
  have hh := (GeometricSiegelBranch.geometricSiegelBranch_holomorphic A P h).continuousOn.comp_continuous
    continuous_subtype_val (fun W : PoissonAutomorphyNormalizationData.Domain (BallGeometryData.FrameIndex A) => W.property)
  rw [continuousOn_iff_continuous_domRestrict]
  exact (hg.comp (PoissonAutomorphyGaussianParabolic.Construction.transformDomain_continuous (RealSymplecticAction.realSymplecticBlocks A P h))).mul hh

theorem branchProduct_square (g h : RationalSU.ArchimedeanSU F H) (Z : AlgebraicGeometry.ComplexMultiplication.CMSiegelMatrix.CM.SiegelMatrix (BallGeometryData.FrameIndex A)) :
    branchProduct A P g h Z.matrix ^ 2 =
      ((RealSymplecticAction.realSymplecticBlocks A P (g * h)).complexify.denominator Z.matrix).det := by
  change (GeometricSiegelBranch.geometricSiegelBranch A P g ((RealSymplecticAction.realSymplecticBlocks A P h).transformSiegel Z).matrix *
    GeometricSiegelBranch.geometricSiegelBranch A P h Z.matrix) ^ 2 = _
  rw [mul_pow, (GeometricSiegelBranch.geometricSiegelBranch_square A P g _).2,
    (GeometricSiegelBranch.geometricSiegelBranch_square A P h _).2, SymplecticComposition.realSymplecticBlocks_mul,
    PoissonAutomorphyGaussianParabolic.Construction.complexify_composeBlocks, PoissonAutomorphyGaussianParabolic.Construction.compose_denominator _ _ _
      ((RealSymplecticAction.realSymplecticBlocks A P h).denominator_det_isUnit Z), Matrix.det_mul]
  rfl

theorem branchProduct_ball (g h : RationalSU.ArchimedeanSU F H) (z : BallNatural.Ball) :
    branchProduct A P g h (PeriodCoordinates.geometricPeriod A P z).matrix = GeometricAutomorphy.geometricFactor A P (g * h) z := by
  change GeometricSiegelBranch.geometricSiegelBranch A P g
    ((RealSymplecticAction.realSymplecticBlocks A P h).transformSiegel (PeriodCoordinates.geometricPeriod A P z)).matrix *
      GeometricSiegelBranch.geometricSiegelBranch A P h (PeriodCoordinates.geometricPeriod A P z).matrix = _
  rw [← CoordinateFrameAction.PeriodCovariance.geometric_period_covariance, GeometricSiegelBranch.geometricSiegelBranch_ball, GeometricSiegelBranch.geometricSiegelBranch_ball,
    GeometricAutomorphy.geometricFactor_mul]

theorem geometricSiegelBranch_mul (g h : RationalSU.ArchimedeanSU F H) (Z : AlgebraicGeometry.ComplexMultiplication.CMSiegelMatrix.CM.SiegelMatrix (BallGeometryData.FrameIndex A)) :
    GeometricSiegelBranch.geometricSiegelBranch A P (g * h) Z.matrix =
      GeometricSiegelBranch.geometricSiegelBranch A P g ((RealSymplecticAction.realSymplecticBlocks A P h).transformSiegel Z).matrix *
        GeometricSiegelBranch.geometricSiegelBranch A P h Z.matrix :=
  (GeometricSiegelBranch.geometricSiegelBranch_unique A P (g * h) (branchProduct A P g h)
    (branchProduct_continuous A P g h) (branchProduct_square A P g h)
    ⟨GeometricSiegelBranch.origin, branchProduct_ball A P g h GeometricSiegelBranch.origin⟩ Z).symm

theorem geometricSiegelBranch_one (Z : AlgebraicGeometry.ComplexMultiplication.CMSiegelMatrix.CM.SiegelMatrix (BallGeometryData.FrameIndex A)) :
    GeometricSiegelBranch.geometricSiegelBranch A P 1 Z.matrix = 1 := by
  apply (GeometricSiegelBranch.geometricSiegelBranch_unique A P 1 (fun _ => 1) continuousOn_const ?_
    ⟨GeometricSiegelBranch.origin, (GeometricAutomorphy.geometricFactor_one A P GeometricSiegelBranch.origin).symm⟩ Z).symm
  intro W
  rw [denominator_of_one _ (SymplecticComposition.realSymplecticBlocks_one A P), Matrix.det_one, one_pow]

end

end OAI.RepresentationTheory.Theta.Adelic.SiegelBranchCocycle

import OAI.RepresentationTheory.Theta.Adelic.SiegelSquareRoot
import OAI.RepresentationTheory.Theta.Adelic.GeometricAutomorphy
import OAI.RepresentationTheory.Theta.Adelic.SymplecticContinuity

/-! # Geometric Siegel Branch -/

namespace OAI.RepresentationTheory.Theta.Adelic.GeometricSiegelBranch

noncomputable section

/-! Extend the independently constructed geometric automorphy branch
to the entire Siegel domain, with joint continuity and unique restriction. -/

open scoped Classical _root_.NumberField _root_.Matrix.Norms.Elementwise

open _root_.Matrix
open OAI.RepresentationTheory.Theta.Adelic.BallGeometryData OAI.RepresentationTheory.Theta.Adelic.BallNatural OAI.RepresentationTheory.Theta.Adelic.RationalSU OAI.RepresentationTheory.Theta.Adelic.GeometricGroup
open OAI.RepresentationTheory.Theta.Adelic.PeriodCoordinates OAI.RepresentationTheory.Theta.Adelic.PeriodHolomorphic OAI.RepresentationTheory.Theta.Adelic.RealSymplecticAction
open OAI.RepresentationTheory.Theta.Adelic.GeometricAutomorphy OAI.RepresentationTheory.Theta.Adelic.GeometricAutomorphy.Holomorphic
open OAI.RepresentationTheory.Theta.Adelic.BallHolomorphicSquare OAI.RepresentationTheory.Theta.Adelic.BallHolomorphicSquare.Root OAI.RepresentationTheory.Theta.Adelic.ContinuousSquareRoot
open OAI.RepresentationTheory.Theta.Adelic.SiegelSquareRoot OAI.RepresentationTheory.Theta.Adelic.SymplecticContinuity

def origin : BallNatural.Ball := ⟨0, by
  change Complex.normSq 0 + Complex.normSq 0 < 1
  norm_num⟩

local instance ballPreconnected : PreconnectedSpace BallNatural.Ball := by
  let : ContractibleSpace BallNatural.Ball := BallHolomorphicSquare.Root.ball_domain_starConvex.contractibleSpace BallHolomorphicSquare.Root.ball_domain_nonempty
  infer_instance

variable {F : Type} [Field F] [NumberField F] {d : F} {m : ℕ}
variable {H : (Matrix (Fin 3) (Fin 3) (Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic F d))ˣ}
variable {K : (Matrix (Fin m) (Fin m) (Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic F d))ˣ}
variable (A : BallGeometryData.BallArithmeticData F d m H K) (P : Weil.AdelicSplitting.Assembly.Construction.GlobalFrames F d 3 m H K)

theorem exists_geometricSiegelBranch :
    ∃ J : RationalSU.ArchimedeanSU F H → Matrix (BallGeometryData.FrameIndex A) (BallGeometryData.FrameIndex A) ℂ → ℂ,
      (∀ g, DifferentiableOn ℂ (J g) (PoissonAutomorphyNormalizationData.siegelSet (BallGeometryData.FrameIndex A))) ∧
      ContinuousOn (fun p => J p.1 p.2)
        ((Set.univ : Set (RationalSU.ArchimedeanSU F H)) ×ˢ PoissonAutomorphyNormalizationData.siegelSet (BallGeometryData.FrameIndex A)) ∧
      (∀ g (Z : AlgebraicGeometry.ComplexMultiplication.CMSiegelMatrix.CM.SiegelMatrix (BallGeometryData.FrameIndex A)), J g Z.matrix ≠ 0 ∧ J g Z.matrix ^ 2 =
        ((RealSymplecticAction.realSymplecticBlocks A P g).complexify.denominator Z.matrix).det) ∧
      (∀ g, J g (PeriodCoordinates.geometricPeriod A P origin).matrix = GeometricAutomorphy.geometricFactor A P g origin) :=
  SiegelSquareRoot.siegel_parameter_square_root (RealSymplecticAction.realSymplecticBlocks A P)
    (SymplecticContinuity.realSymplecticBlocks_C_continuous A P) (SymplecticContinuity.realSymplecticBlocks_D_continuous A P)
    (PeriodCoordinates.geometricPeriod A P origin) (fun g => GeometricAutomorphy.geometricFactor A P g origin)
    (BallHolomorphicSquare.continuous_fixed_right (GeometricAutomorphy.geometricFactor A P) (GeometricAutomorphy.geometricFactor_continuous A P) origin)
    (fun g => GeometricAutomorphy.geometricFactor_square A P g origin)

def geometricSiegelBranch := (exists_geometricSiegelBranch A P).choose

theorem geometricSiegelBranch_holomorphic (g : RationalSU.ArchimedeanSU F H) :
    DifferentiableOn ℂ (geometricSiegelBranch A P g) (PoissonAutomorphyNormalizationData.siegelSet (BallGeometryData.FrameIndex A)) :=
  (exists_geometricSiegelBranch A P).choose_spec.1 g

theorem geometricSiegelBranch_continuous :
    ContinuousOn (fun p => geometricSiegelBranch A P p.1 p.2)
      ((Set.univ : Set (RationalSU.ArchimedeanSU F H)) ×ˢ PoissonAutomorphyNormalizationData.siegelSet (BallGeometryData.FrameIndex A)) :=
  (exists_geometricSiegelBranch A P).choose_spec.2.1

theorem geometricSiegelBranch_square (g : RationalSU.ArchimedeanSU F H) (Z : AlgebraicGeometry.ComplexMultiplication.CMSiegelMatrix.CM.SiegelMatrix (BallGeometryData.FrameIndex A)) :
    geometricSiegelBranch A P g Z.matrix ≠ 0 ∧
      geometricSiegelBranch A P g Z.matrix ^ 2 =
        ((RealSymplecticAction.realSymplecticBlocks A P g).complexify.denominator Z.matrix).det :=
  (exists_geometricSiegelBranch A P).choose_spec.2.2.1 g Z

theorem geometricSiegelBranch_origin (g : RationalSU.ArchimedeanSU F H) :
    geometricSiegelBranch A P g (PeriodCoordinates.geometricPeriod A P origin).matrix = GeometricAutomorphy.geometricFactor A P g origin :=
  (exists_geometricSiegelBranch A P).choose_spec.2.2.2 g

theorem geometricSiegelBranch_ball (g : RationalSU.ArchimedeanSU F H) (z : BallNatural.Ball) :
    geometricSiegelBranch A P g (PeriodCoordinates.geometricPeriod A P z).matrix = GeometricAutomorphy.geometricFactor A P g z := by
  have hJ : Continuous (fun z => geometricSiegelBranch A P g (PeriodCoordinates.geometricPeriod A P z).matrix) :=
    (geometricSiegelBranch_holomorphic A P g).continuousOn.comp_continuous
      (BallHolomorphicSquare.ball_holomorphic_continuous _ (PeriodHolomorphic.period_matrix_holomorphic A P))
      (fun z => ⟨(PeriodCoordinates.geometricPeriod A P z).symmetric, (PeriodCoordinates.geometricPeriod A P z).imaginary_posDef⟩)
  have he := ContinuousSquareRoot.continuous_square_roots_eq _ _ hJ
    (BallHolomorphicSquare.continuous_fixed_left (GeometricAutomorphy.geometricFactor A P) (GeometricAutomorphy.geometricFactor_continuous A P) g)
    (fun z => (geometricSiegelBranch_square A P g (PeriodCoordinates.geometricPeriod A P z)).1)
    (fun z => (geometricSiegelBranch_square A P g (PeriodCoordinates.geometricPeriod A P z)).2.trans
      (GeometricAutomorphy.geometricFactor_square A P g z).symm) origin (geometricSiegelBranch_origin A P g)
  exact congrFun he z

theorem geometricSiegelBranch_unique (g : RationalSU.ArchimedeanSU F H)
    (j : Matrix (BallGeometryData.FrameIndex A) (BallGeometryData.FrameIndex A) ℂ → ℂ)
    (hj : ContinuousOn j (PoissonAutomorphyNormalizationData.siegelSet (BallGeometryData.FrameIndex A)))
    (hs : ∀ Z : AlgebraicGeometry.ComplexMultiplication.CMSiegelMatrix.CM.SiegelMatrix (BallGeometryData.FrameIndex A),
      j Z.matrix ^ 2 = ((RealSymplecticAction.realSymplecticBlocks A P g).complexify.denominator Z.matrix).det)
    (hb : ∃ z, j (PeriodCoordinates.geometricPeriod A P z).matrix = GeometricAutomorphy.geometricFactor A P g z)
    (Z : AlgebraicGeometry.ComplexMultiplication.CMSiegelMatrix.CM.SiegelMatrix (BallGeometryData.FrameIndex A)) : j Z.matrix = geometricSiegelBranch A P g Z.matrix := by
  obtain ⟨z, hz⟩ := hb
  have hcJ : Continuous (fun W : PoissonAutomorphyNormalizationData.Domain (BallGeometryData.FrameIndex A) => geometricSiegelBranch A P g W.val) :=
    (geometricSiegelBranch_holomorphic A P g).continuousOn.comp_continuous
      continuous_subtype_val (fun W => W.property)
  have hcj : Continuous (fun W : PoissonAutomorphyNormalizationData.Domain (BallGeometryData.FrameIndex A) => j W.val) :=
    hj.comp_continuous continuous_subtype_val (fun W => W.property)
  have he := ContinuousSquareRoot.continuous_square_roots_eq _ _ hcJ hcj
    (fun W => (geometricSiegelBranch_square A P g (PoissonAutomorphyNormalizationData.toSiegel W)).1)
    (fun W => (geometricSiegelBranch_square A P g (PoissonAutomorphyNormalizationData.toSiegel W)).2.trans (hs (PoissonAutomorphyNormalizationData.toSiegel W)).symm)
    (PoissonAutomorphyNormalizationData.ofSiegel (PeriodCoordinates.geometricPeriod A P z)) ((geometricSiegelBranch_ball A P g z).trans hz.symm)
  exact (congrFun he (PoissonAutomorphyNormalizationData.ofSiegel Z)).symm

end

end OAI.RepresentationTheory.Theta.Adelic.GeometricSiegelBranch

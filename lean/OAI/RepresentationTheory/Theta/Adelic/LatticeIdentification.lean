import OAI.RepresentationTheory.Theta.Adelic.SupportLattice
import OAI.RepresentationTheory.Theta.Adelic.GeometricGaussians
import OAI.RepresentationTheory.Theta.Adelic.DataTheta

/-! # Lattice Identification -/

namespace OAI.RepresentationTheory.Theta.Adelic.LatticeIdentification

noncomputable section

/-! Exact identification of the rational theta sum and its completed
Taylor tensors with the CompletedTheta construction on the actual support lattice. -/

open scoped Classical _root_.NumberField BoundedContinuousFunction

open OAI.RepresentationTheory.Theta.Adelic.BallGeometryData OAI.RepresentationTheory.Theta.Adelic.DataTheta OAI.RepresentationTheory.Theta.Adelic.DataTheta.Descent OAI.RepresentationTheory.Theta.Adelic.FiniteSchwartz
open OAI.RepresentationTheory.Theta.Adelic.MinkowskiCoordinatesPosition OAI.RepresentationTheory.Theta.Adelic.SupportLattice OAI.RepresentationTheory.Theta.Adelic.GeometricGaussians

variable {F : Type} [Field F] [NumberField F] {d : F} {m : ℕ}
variable {H : (Matrix (Fin 3) (Fin 3) (Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic F d))ˣ}
variable {K : (Matrix (Fin m) (Fin m) (Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic F d))ˣ}
variable (A : BallGeometryData.BallArithmeticData F d m H K) (P : Weil.AdelicSplitting.Assembly.Construction.GlobalFrames F d 3 m H K)

theorem latticeRationalPoint_injective (f : FiniteSchwartz.finiteSchwartz F (3 * m)) :
    Function.Injective (SupportLattice.latticeRationalPoint A f) := by
  intro l t h
  apply Subtype.ext
  rw [← SupportLattice.latticeRationalPoint_spec A f l, ← SupportLattice.latticeRationalPoint_spec A f t, h]

theorem thetaSummand_support_lattice (f : FiniteSchwartz.finiteSchwartz F (3 * m))
    (Z : Matrix (BallGeometryData.FrameIndex A) (BallGeometryData.FrameIndex A) ℂ) (ξ : BallGeometryData.FrameIndex A → ℂ) :
    Function.support (DataTheta.thetaSummand (GeometricGaussians.constructedComparison A P) f Z ξ) ⊆
      Set.range (SupportLattice.latticeRationalPoint A f) := by
  intro x hx
  have hw : DataTheta.rationalWeight f x ≠ 0 := by
    intro hzero
    apply hx
    simp only [DataTheta.thetaSummand, hzero, zero_mul]
  exact ⟨⟨fun i => (MinkowskiCoordinatesPosition.rationalPositionCoordinates A x i : ℝ), SupportLattice.rationalWeight_support A f x hw⟩,
    SupportLattice.latticeRationalPoint_of_rational A f x _⟩

theorem thetaSummand_lattice (f : FiniteSchwartz.finiteSchwartz F (3 * m))
    (Z : Matrix (BallGeometryData.FrameIndex A) (BallGeometryData.FrameIndex A) ℂ) (ξ : BallGeometryData.FrameIndex A → ℂ) (l : SupportLattice.supportLattice A f) :
    DataTheta.thetaSummand (GeometricGaussians.constructedComparison A P) f Z ξ (SupportLattice.latticeRationalPoint A f l) =
      SupportLattice.latticeWeight A f l * DataTheta.gaussianValue Z ξ l.val := by
  change DataTheta.rationalWeight f (SupportLattice.latticeRationalPoint A f l) * DataTheta.gaussianValue Z ξ
    (fun i => (MinkowskiCoordinatesPosition.rationalPositionCoordinates A (SupportLattice.latticeRationalPoint A f l) i : ℝ)) = _
  rw [SupportLattice.latticeRationalPoint_spec, SupportLattice.latticeWeight_apply]

theorem rationalTheta_lattice (f : FiniteSchwartz.finiteSchwartz F (3 * m))
    (Z : Matrix (BallGeometryData.FrameIndex A) (BallGeometryData.FrameIndex A) ℂ) (ξ : BallGeometryData.FrameIndex A → ℂ) :
    DataTheta.rationalTheta (GeometricGaussians.constructedComparison A P) f Z ξ =
      Definitions.theta (SupportLattice.supportLattice A f) (SupportLattice.latticeWeight A f) Z ξ := by
  change (∑' x, DataTheta.thetaSummand (GeometricGaussians.constructedComparison A P) f Z ξ x) =
    ∑' l : SupportLattice.supportLattice A f, SupportLattice.latticeWeight A f l * DataTheta.gaussianValue Z ξ l.val
  rw [← (latticeRationalPoint_injective A f).tsum_eq (thetaSummand_support_lattice A P f Z ξ)]
  apply tsum_congr
  intro l
  exact thetaSummand_lattice A P f Z ξ l

theorem completedTheta_lattice (f : FiniteSchwartz.finiteSchwartz F (3 * m))
    (Z : Matrix (BallGeometryData.FrameIndex A) (BallGeometryData.FrameIndex A) ℂ) (ξ : BallGeometryData.FrameIndex A → ℂ) :
    DataTheta.completedTheta (GeometricGaussians.constructedComparison A P) f Z ξ =
      Definitions.completedTheta (SupportLattice.supportLattice A f) (SupportLattice.latticeWeight A f) Z ξ := by
  rw [DataTheta.completedTheta, Definitions.completedTheta, rationalTheta_lattice]

theorem completedTensor_lattice (f : FiniteSchwartz.finiteSchwartz F (3 * m)) (a : ℕ)
    (Z : Matrix (BallGeometryData.FrameIndex A) (BallGeometryData.FrameIndex A) ℂ) :
    DataTheta.completedTensor (GeometricGaussians.constructedComparison A P) f a Z =
      Definitions.completedTensor (SupportLattice.supportLattice A f) (SupportLattice.latticeWeight A f) a Z := by
  have he := funext (completedTheta_lattice A P f Z)
  simp only [DataTheta.completedTensor, Definitions.completedTensor, he]

theorem constructedComparison_lattice : DataTheta.Descent.LatticeIdentification (GeometricGaussians.constructedComparison A P) := by
  intro f
  refine ⟨SupportLattice.supportLattice A f, inferInstance, SupportLattice.latticeWeight A f, SupportLattice.supportLattice_rational A f,
    ?_, SupportLattice.latticeWeight_rational A f, ?_, ?_⟩
  · intro x hx
    by_contra hw
    exact hx (SupportLattice.rationalWeight_support A f x hw)
  · intro Z ξ
    exact ⟨rationalTheta_lattice A P f Z.matrix ξ, completedTheta_lattice A P f Z.matrix ξ⟩
  · intro a Z
    exact completedTensor_lattice A P f a Z.matrix

theorem rationalTheta_summable (f : FiniteSchwartz.finiteSchwartz F (3 * m))
    (Z : AlgebraicGeometry.ComplexMultiplication.CMSiegelMatrix.CM.SiegelMatrix (BallGeometryData.FrameIndex A)) (ξ : BallGeometryData.FrameIndex A → ℂ) :
    Summable (DataTheta.thetaSummand (GeometricGaussians.constructedComparison A P) f Z.matrix ξ) := by
  have hl : Summable (fun l : SupportLattice.supportLattice A f => SupportLattice.latticeWeight A f l * DataTheta.gaussianValue Z.matrix ξ l.val) := by
    have h := (Z.phase.weightedThetaTerm_norm_summable (AlgebraicGeometry.ComplexMultiplication.ThetaCoordinates.CM.thetaCoordinatePairing (BallGeometryData.FrameIndex A))
      (SupportLattice.supportLattice A f) (SupportLattice.latticeWeight A f) ξ).of_norm
    simpa only [AlgebraicGeometry.ComplexMultiplication.CMSiegelPhase.CM.SiegelPhase.weightedThetaTerm, AlgebraicGeometry.ComplexMultiplication.CMSiegelPhase.CM.SiegelPhase.thetaTerm, AlgebraicGeometry.ComplexMultiplication.CMSiegelMatrix.CM.SiegelMatrix.phase,
      AlgebraicGeometry.ComplexMultiplication.ThetaCoordinates.CM.thetaCoordinatePairing_apply, DataTheta.gaussianValue] using h
  have hr : Summable (fun l : SupportLattice.supportLattice A f =>
      DataTheta.thetaSummand (GeometricGaussians.constructedComparison A P) f Z.matrix ξ (SupportLattice.latticeRationalPoint A f l)) :=
    hl.congr (fun l => (thetaSummand_lattice A P f Z.matrix ξ l).symm)
  exact ((latticeRationalPoint_injective A f).summable_iff
    (fun x hx => by
      by_contra hzero
      exact hx (thetaSummand_support_lattice A P f Z.matrix ξ hzero))).mp hr

end

end OAI.RepresentationTheory.Theta.Adelic.LatticeIdentification

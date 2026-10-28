import OAI.RepresentationTheory.Theta.Adelic.LatticeIdentification
import OAI.RepresentationTheory.Theta.Adelic.Prerequisites

/-! # Regularity -/

namespace OAI.RepresentationTheory.Theta.Adelic.Regularity

noncomputable section

/-! Apply the full CompletedTheta prerequisite to the identity transformation.
Its Poisson hypothesis is then an identity, giving regularity and
symmetry of the actual completed lattice and rational theta tensors. -/

open scoped Classical _root_.NumberField BoundedContinuousFunction _root_.Matrix.Norms.Elementwise

open _root_.Matrix
open OAI.RepresentationTheory.Theta.Adelic.BallGeometryData OAI.RepresentationTheory.Theta.Adelic.DataTheta OAI.RepresentationTheory.Theta.Adelic.FiniteSchwartz OAI.RepresentationTheory.Theta.Adelic.GeometricGaussians
open OAI.RepresentationTheory.Theta.Adelic.SupportLattice OAI.RepresentationTheory.Theta.Adelic.LatticeIdentification OAI.RepresentationTheory.Theta.Adelic.Prerequisites

variable (I : Type) [Fintype I] [DecidableEq I]

def identityBlocks (R : Type) [CommRing R] : AlgebraicGeometry.ComplexMultiplication.CMSymplecticSiegel.CM.SymplecticBlocks I R where
  A := 1
  B := 0
  C := 0
  D := 1
  symplectic := by
    rw [Matrix.fromBlocks_one]
    exact (Matrix.symplecticGroup I R).one_mem

theorem identity_denominator (Z : Matrix I I ℂ) :
    (identityBlocks I ℝ).complexify.denominator Z = 1 := by
  simp [identityBlocks, AlgebraicGeometry.ComplexMultiplication.CMSymplecticSiegel.CM.SymplecticBlocks.complexify, AlgebraicGeometry.ComplexMultiplication.CMSymplecticSiegel.CM.SymplecticBlocks.denominator]

theorem identity_transform (Z : AlgebraicGeometry.ComplexMultiplication.CMSiegelMatrix.CM.SiegelMatrix I) : (identityBlocks I ℝ).transformSiegel Z = Z := by
  apply CoordinateFrameAction.PeriodCovariance.siegel_matrix_ext
  simp [AlgebraicGeometry.ComplexMultiplication.CMSymplecticSiegel.CM.SymplecticBlocks.transformSiegel_matrix, AlgebraicGeometry.ComplexMultiplication.CMSymplecticSiegel.CM.SymplecticBlocks.complexify, identityBlocks]

theorem identity_jacobi (Z : AlgebraicGeometry.ComplexMultiplication.CMSiegelMatrix.CM.SiegelMatrix I) (ξ : I → ℂ) :
    (identityBlocks I ℝ).jacobiChange Z ξ = ξ := by
  rw [AlgebraicGeometry.ComplexMultiplication.CMSymplecticSiegel.CM.SymplecticBlocks.jacobiChange_apply, identity_denominator]
  simp

theorem identity_correction (Z : AlgebraicGeometry.ComplexMultiplication.CMSiegelMatrix.CM.SiegelMatrix I) (ξ : I → ℂ) :
    (identityBlocks I ℝ).thetaCorrectionForm Z ξ ξ = 0 := by
  rw [AlgebraicGeometry.ComplexMultiplication.CMSymplecticSiegel.CM.SymplecticBlocks.thetaCorrectionForm_apply, identity_denominator]
  simp [identityBlocks, AlgebraicGeometry.ComplexMultiplication.CMSymplecticSiegel.CM.SymplecticBlocks.complexify]

theorem lattice_tensor_regularity (h : Prerequisites.ThetaInput.{0}) (L : Submodule ℤ (I → ℝ))
    [DiscreteTopology L] (φ : L →ᵇ ℂ) :
    (∀ a : ℕ, ContDiffOn ℝ ⊤ (Definitions.completedTensor L φ a) Definitions.siegelDomain) ∧
    (∀ (a : ℕ) (Z : AlgebraicGeometry.ComplexMultiplication.CMSiegelMatrix.CM.SiegelMatrix I) (σ : Equiv.Perm (Fin a)) v,
      Definitions.completedTensor L φ a Z.matrix (fun i => v (σ i)) = Definitions.completedTensor L φ a Z.matrix v) := by
  have hA : (identityBlocks I ℝ).A = (identityBlocks I ℚ).A.map (algebraMap ℚ ℝ) := by
    simp [identityBlocks]
  have hB : (identityBlocks I ℝ).B = (identityBlocks I ℚ).B.map (algebraMap ℚ ℝ) := by
    simp [identityBlocks]
  have hC : (identityBlocks I ℝ).C = (identityBlocks I ℚ).C.map (algebraMap ℚ ℝ) := by
    simp [identityBlocks]
  have hD : (identityBlocks I ℝ).D = (identityBlocks I ℚ).D.map (algebraMap ℚ ℝ) := hA
  have hh (Z : AlgebraicGeometry.ComplexMultiplication.CMSiegelMatrix.CM.SiegelMatrix I) : (1 : ℂ) ^ 2 =
      ((identityBlocks I ℝ).complexify.denominator Z.matrix).det := by
    rw [identity_denominator, Matrix.det_one, one_pow]
  have hp (Z : AlgebraicGeometry.ComplexMultiplication.CMSiegelMatrix.CM.SiegelMatrix I) (ξ : I → ℂ) :
      Definitions.theta L φ ((identityBlocks I ℝ).transformSiegel Z).matrix
        ((identityBlocks I ℝ).jacobiChange Z ξ) =
      1 * (Complex.exp ((identityBlocks I ℝ).thetaCorrectionForm Z ξ ξ) * Definitions.theta L φ Z.matrix ξ) := by
    rw [identity_transform, identity_jacobi, identity_correction, Complex.exp_zero, one_mul, one_mul]
  have ht := h L L φ φ (identityBlocks I ℚ) (identityBlocks I ℝ) hA hB hC hD (fun _ => 1) hh hp
  exact ⟨ht.1, ht.2.1⟩

variable {F : Type} [Field F] [NumberField F] {d : F} {m : ℕ}
variable {H : (Matrix (Fin 3) (Fin 3) (Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic F d))ˣ}
variable {K : (Matrix (Fin m) (Fin m) (Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic F d))ˣ}
variable (A : BallGeometryData.BallArithmeticData F d m H K) (P : Weil.AdelicSplitting.Assembly.Construction.GlobalFrames F d 3 m H K)

theorem completedTensor_smooth (h : Prerequisites.ThetaInput.{0}) (f : FiniteSchwartz.finiteSchwartz F (3 * m)) (a : ℕ) :
    ContDiffOn ℝ ⊤ (DataTheta.completedTensor (GeometricGaussians.constructedComparison A P) f a) Definitions.siegelDomain := by
  have he := funext (LatticeIdentification.completedTensor_lattice A P f a)
  rw [he]
  exact (lattice_tensor_regularity (BallGeometryData.FrameIndex A) h (SupportLattice.supportLattice A f) (SupportLattice.latticeWeight A f)).1 a

theorem completedTensor_symmetric (h : Prerequisites.ThetaInput.{0}) (f : FiniteSchwartz.finiteSchwartz F (3 * m)) (a : ℕ)
    (Z : AlgebraicGeometry.ComplexMultiplication.CMSiegelMatrix.CM.SiegelMatrix (BallGeometryData.FrameIndex A)) (σ : Equiv.Perm (Fin a)) (v : Fin a → BallGeometryData.FrameIndex A → ℂ) :
    DataTheta.completedTensor (GeometricGaussians.constructedComparison A P) f a Z.matrix (fun i => v (σ i)) =
      DataTheta.completedTensor (GeometricGaussians.constructedComparison A P) f a Z.matrix v := by
  rw [LatticeIdentification.completedTensor_lattice]
  exact (lattice_tensor_regularity (BallGeometryData.FrameIndex A) h (SupportLattice.supportLattice A f) (SupportLattice.latticeWeight A f)).2 a Z σ v

end

end OAI.RepresentationTheory.Theta.Adelic.Regularity

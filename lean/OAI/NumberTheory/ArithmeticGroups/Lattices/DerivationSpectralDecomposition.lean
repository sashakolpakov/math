import OAI.NumberTheory.ArithmeticGroups.Lattices.InvolutionSpectralDecomposition
import OAI.NumberTheory.ArithmeticGroups.Lattices.OrthogonalBracketAlgebra

/-! # Derivation Spectral Decomposition -/

namespace OAI.NumberTheory.ArithmeticGroups.Lattices.DerivationSpectralDecomposition.Construction

noncomputable section

section

/-! The derivations of an adjoint-stable bracket split into skew-adjoint,
symmetric centralizing, and positive commutator-eigenvalue directions. -/

open scoped Classical
open _root_.ContinuousLinearMap _root_.Module.End

variable {L : Type*} [NormedAddCommGroup L] [InnerProductSpace ℝ L] [FiniteDimensional ℝ L]

def bracketDerivationSubmodule (B : L →L[ℝ] L →L[ℝ] L) : Submodule ℝ (L →L[ℝ] L) :=
  (Lie.AutomorphismTransversal.Construction.continuousBilinearDerivationDefect B).toLinearMap.ker

def positiveBracketDerivations (B : L →L[ℝ] L →L[ℝ] L) (H : L →L[ℝ] L) :
    Submodule ℝ (L →L[ℝ] L) :=
  InvolutionSpectralDecomposition.Construction.positiveSpectralSubmodule (EndomorphismHilbertSchmidt.Construction.continuousCommutatorRepresentation H).toLinearMap (bracketDerivationSubmodule B)

def continuousEndAdjointLinearMap [CompleteSpace L] :
    (L →L[ℝ] L) →ₗ[ℝ] (L →L[ℝ] L) := (starLinearEquiv ℝ).toLinearMap

def skewBracketDerivations [CompleteSpace L] (B : L →L[ℝ] L →L[ℝ] L) : Submodule ℝ (L →L[ℝ] L) :=
  bracketDerivationSubmodule B ⊓ (continuousEndAdjointLinearMap (L := L) + LinearMap.id).ker

theorem selfAdjoint_commutator_invariant_eigenspace_span [CompleteSpace L]
    (H : L →L[ℝ] L) (hH : H.toLinearMap.IsSymmetric)
    (P : Submodule ℝ (L →L[ℝ] L)) (hP : ∀ X ∈ P, H * X - X * H ∈ P) :
    P = ⨆ r : ℝ, P ⊓ eigenspace (EndomorphismHilbertSchmidt.Construction.continuousCommutatorRepresentation H).toLinearMap r := by
  let b := stdOrthonormalBasis ℝ L
  exact InvariantSymmetricEigenspaces.Construction.equiv_symmetric_invariant_eigenspace_span (EndomorphismHilbertSchmidt.Construction.continuousEndEuclideanCoordinates b.toBasis).toLinearEquiv
    (EndomorphismHilbertSchmidt.Construction.continuousCommutatorRepresentation H).toLinearMap (EndomorphismHilbertSchmidt.Construction.euclideanCommutatorRepresentation b H).toLinearMap
    (EndomorphismHilbertSchmidt.Construction.euclideanCommutatorRepresentation_isSymmetric b H hH)
    (EndomorphismHilbertSchmidt.Construction.euclideanCommutatorRepresentation_apply b H) P hP

theorem bracket_derivation_spectral_decomposition [CompleteSpace L]
    (B : L →L[ℝ] L →L[ℝ] L)
    (hadj : ∀ X, Lie.AutomorphismTransversal.Construction.continuousBilinearDerivationDefect B X = 0 →
      Lie.AutomorphismTransversal.Construction.continuousBilinearDerivationDefect B (adjoint X) = 0)
    (H : L →L[ℝ] L) (hH : H ∈ RegularSymmetricDerivation.Construction.symmetricDerivationSubmodule B) :
    bracketDerivationSubmodule B =
      skewBracketDerivations B ⊔
      (bracketDerivationSubmodule B ⊓ (EndomorphismHilbertSchmidt.Construction.continuousCommutatorRepresentation H).toLinearMap.ker ⊓
        (continuousEndAdjointLinearMap (L := L) - LinearMap.id).ker) ⊔ positiveBracketDerivations B H := by
  let A := (EndomorphismHilbertSchmidt.Construction.continuousCommutatorRepresentation H).toLinearMap
  let J : (L →L[ℝ] L) →ₗ[ℝ] (L →L[ℝ] L) := continuousEndAdjointLinearMap
  have hJ (X : L →L[ℝ] L) : J (J X) = X := star_star X
  have hAJ (X : L →L[ℝ] L) : A (J X) = -J (A X) := by
    change H * adjoint X - adjoint X * H = -adjoint (H * X - X * H)
    rw [map_sub]
    simp only [mul_def, adjoint_comp, hH.1.clm_adjoint_eq]
    abel
  have hspan := selfAdjoint_commutator_invariant_eigenspace_span H hH.1 (bracketDerivationSubmodule B)
    (fun X hX => OrthogonalBracketAlgebra.Construction.bracket_derivation_commutator B H X hH.2 hX)
  exact InvolutionSpectralDecomposition.Construction.involution_spectral_decomposition A J hJ hAJ (bracketDerivationSubmodule B) hspan hadj

end

/-! Positive commutator eigenspaces of bracket derivations are closed
under commutators and stable under derivations centralizing the symmetric element. -/

open _root_.ContinuousLinearMap _root_.Module.End

theorem algebra_commutator_eigen_sum
    {A : Type*} [Ring A] [Algebra ℝ A] (H X Y : A) (r s : ℝ)
    (hX : H * X - X * H = r • X) (hY : H * Y - Y * H = s • Y) :
    H * (X * Y - Y * X) - (X * Y - Y * X) * H = (r + s) • (X * Y - Y * X) := by
  calc
    _ = (H * X - X * H) * Y + X * (H * Y - Y * H) -
        (H * Y - Y * H) * X - Y * (H * X - X * H) := by noncomm_ring
    _ = _ := by
      rw [hX, hY]
      simp only [smul_mul_assoc, mul_smul_comm, add_smul, smul_sub]
      abel

variable {L : Type*} [NormedAddCommGroup L] [InnerProductSpace ℝ L] [FiniteDimensional ℝ L]

theorem nonnegative_eigen_commutator_positive
    (B : L →L[ℝ] L →L[ℝ] L) (H X : L →L[ℝ] L)
    (hX : X ∈ bracketDerivationSubmodule B) {r : ℝ} (hr : 0 ≤ r)
    (hXe : H * X - X * H = r • X) :
    positiveBracketDerivations B H ≤
      (positiveBracketDerivations B H).comap (EndomorphismHilbertSchmidt.Construction.continuousCommutatorRepresentation X).toLinearMap := by
  apply iSup_le
  intro s
  apply iSup_le
  intro hs Y hY
  change X * Y - Y * X ∈ positiveBracketDerivations B H
  apply InvolutionSpectralDecomposition.Construction.mem_positiveSpectralSubmodule _ _ (add_pos_of_nonneg_of_pos hr hs)
  · exact OrthogonalBracketAlgebra.Construction.bracket_derivation_commutator B X Y hX hY.1
  · exact algebra_commutator_eigen_sum H X Y r s hXe (mem_eigenspace_iff.mp hY.2)

theorem positiveBracketDerivations_commutator
    (B : L →L[ℝ] L →L[ℝ] L) (H X Y : L →L[ℝ] L)
    (hX : X ∈ positiveBracketDerivations B H) (hY : Y ∈ positiveBracketDerivations B H) :
    X * Y - Y * X ∈ positiveBracketDerivations B H := by
  have hle : positiveBracketDerivations B H ≤
      (positiveBracketDerivations B H).comap (-(EndomorphismHilbertSchmidt.Construction.continuousCommutatorRepresentation Y).toLinearMap) := by
    apply iSup_le
    intro r
    apply iSup_le
    intro hr Z hZ
    have he := nonnegative_eigen_commutator_positive B H Z hZ.1 hr.le (mem_eigenspace_iff.mp hZ.2) hY
    change -(Y * Z - Z * Y) ∈ positiveBracketDerivations B H
    have hneg : -(Y * Z - Z * Y) = Z * Y - Y * Z := by abel
    rw [hneg]
    exact he
  have he := hle hX
  change -(Y * X - X * Y) ∈ positiveBracketDerivations B H at he
  have hneg : -(Y * X - X * Y) = X * Y - Y * X := by abel
  rwa [hneg] at he

theorem centralizing_derivation_commutator_positive
    (B : L →L[ℝ] L →L[ℝ] L) (H X Y : L →L[ℝ] L)
    (hX : X ∈ bracketDerivationSubmodule B) (hHX : Commute H X)
    (hY : Y ∈ positiveBracketDerivations B H) : X * Y - Y * X ∈ positiveBracketDerivations B H := by
  have he : H * X - X * H = (0 : ℝ) • X := by rw [zero_smul, sub_eq_zero.mpr hHX.eq]
  exact nonnegative_eigen_commutator_positive B H X hX le_rfl he hY

end

end OAI.NumberTheory.ArithmeticGroups.Lattices.DerivationSpectralDecomposition.Construction

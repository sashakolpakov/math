import OAI.AlgebraicGeometry.ComplexMultiplication.SiegelThetaSpanning
import Mathlib.Algebra.Module.ZLattice.Basic

/-! # Theta Coordinates -/

namespace OAI.AlgebraicGeometry.ComplexMultiplication.ThetaCoordinates.CM

noncomputable section

/-!
# Standard coordinates for the sparse theta gradient theorem

The position space is `ι → ℝ`, the Jacobi space is `ι → ℂ`, and the
lattice is the integer span of the standard real basis. The pairing is
the actual coordinate dot product. Its lattice values span the full
complex cotangent space, so the theta gradient theorem has no additional
spanning hypothesis in these coordinates.
-/

open scoped Classical

variable (ι : Type*) [Fintype ι]

def thetaCoordinateLattice : Submodule ℤ (ι → ℝ) :=
  Submodule.span ℤ (Set.range (Pi.basisFun ℝ ι))

instance : DiscreteTopology (thetaCoordinateLattice ι) :=
  inferInstanceAs (DiscreteTopology (Submodule.span ℤ (Set.range (Pi.basisFun ℝ ι))))

def thetaCoordinateLatticeBasis (i : ι) : thetaCoordinateLattice ι :=
  ⟨(Pi.basisFun ℝ ι) i, Submodule.subset_span ⟨i, rfl⟩⟩

def thetaCoordinatePairing : (ι → ℝ) →L[ℝ] ((ι → ℂ) →L[ℂ] ℂ) :=
  ∑ i : ι, (ContinuousLinearMap.proj i : (ι → ℝ) →L[ℝ] ℝ).smulRight
    (ContinuousLinearMap.proj i : (ι → ℂ) →L[ℂ] ℂ)

theorem thetaCoordinatePairing_apply (x : ι → ℝ) (z : ι → ℂ) :
    thetaCoordinatePairing ι x z = ∑ i, (x i : ℂ) * z i := by
  simp [thetaCoordinatePairing, Complex.real_smul]

theorem thetaCoordinatePairing_basis (i : ι) :
    thetaCoordinatePairing ι ((Pi.basisFun ℝ ι) i) = ContinuousLinearMap.proj i := by
  ext z
  simp [thetaCoordinatePairing_apply, Pi.basisFun_apply, Pi.single_apply, apply_ite]

theorem span_thetaCoordinatePairing_eq_top :
    Submodule.span ℂ (Set.range (fun x : thetaCoordinateLattice ι =>
      thetaCoordinatePairing ι x)) = ⊤ := by
  apply top_unique
  intro f _
  have hf : f = ∑ i : ι, f ((Pi.basisFun ℂ ι) i) •
      thetaCoordinatePairing ι ((Pi.basisFun ℝ ι) i) := by
    ext z
    have hz : (∑ i : ι, z i • (Pi.basisFun ℂ ι) i) = z := by
      simpa only [Pi.basisFun_repr] using (Pi.basisFun ℂ ι).sum_repr z
    calc
      f z = f (∑ i : ι, z i • (Pi.basisFun ℂ ι) i) := congrArg f hz.symm
      _ = _ := by
        simp only [map_sum, map_smul, sum_apply, smul_apply,
          thetaCoordinatePairing_basis, ContinuousLinearMap.proj_apply, smul_eq_mul, mul_comm]
  rw [hf]
  apply Submodule.sum_mem
  intro i _
  apply Submodule.smul_mem
  exact Submodule.subset_span ⟨thetaCoordinateLatticeBasis ι i, rfl⟩

/-- Actual first derivatives of positive-degree sparse theta inputs span
the whole standard cotangent space for every positive Siegel phase. -/
theorem span_coordinate_sparseThetaGradients_eq_top (Z : CMSiegelPhase.CM.SiegelPhase (ι → ℝ)) :
    Submodule.span ℂ (Set.range (fun an : thetaCoordinateLattice ι × ℕ =>
      Z.sparseThetaGradient (thetaCoordinatePairing ι) (thetaCoordinateLattice ι)
        an.1 an.2)) = ⊤ :=
  Z.span_sparseThetaGradients_eq_top (thetaCoordinatePairing ι) (thetaCoordinateLattice ι)
    (span_thetaCoordinatePairing_eq_top ι)

end

end OAI.AlgebraicGeometry.ComplexMultiplication.ThetaCoordinates.CM

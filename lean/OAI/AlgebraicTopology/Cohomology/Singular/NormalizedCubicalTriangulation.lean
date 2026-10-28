import OAI.AlgebraicTopology.Cohomology.Singular.CubicalDegenerate
import OAI.AlgebraicTopology.Cohomology.Singular.Normalized
import OAI.AlgebraicTopology.DeRham.Comparison.CubicalDegenerateQ
import Mathlib.GroupTheory.Perm.Sign
import Mathlib.LinearAlgebra.Finsupp.LinearCombination

/-! # Normalized Cubical Triangulation -/

namespace OAI.AlgebraicTopology.Cohomology.Singular.NormalizedCubicalTriangulation

noncomputable section

/-!
# Degreewise signed triangulation on normalized cubical chains

A smooth cube is sent to the signed sum of its actual permutation simplices.
After simplicial normalization every coordinate-degenerate cube maps to zero,
so this linear map descends through the genuine normalized cubical quotient.
The source and target are actual integral chain groups.

This file supplies degreewise maps and quotient compatibility. It does not
assert compatibility with the boundary operators, which requires the separate
endpoint and sign calculations.
-/

open _root_.CategoryTheory
open OAI.AlgebraicTopology.DeRham.Comparison.CubicalDegenerateQ
open scoped BigOperators Simplicial

variable {n m : ℕ}

/-- The actual smooth singular complex with integral coefficients. -/
abbrev smoothIntegralChains (m : ℕ) : ChainComplex (ModuleCat.{0} ℤ) ℕ :=
  (Smooth.smoothSingularSubcomplex (Fin m → ℝ)).toSSet.chainComplex (ModuleCat.of ℤ ℤ)

/-- Mathlib's actual normalization of the smooth integral singular complex. -/
abbrev normalizedSmoothIntegralChains (m : ℕ) : ChainComplex (ModuleCat.{0} ℤ) ℕ :=
  (Smooth.smoothSingularSubcomplex (Fin m → ℝ)).toSSet.normalizedChainComplex (ModuleCat.of ℤ ℤ)

/-- A cube's signed permutation triangulation in the ordinary smooth chain group. -/
def signedCubeTriangulation (cube : DeRham.Comparison.StokesF.SingularCubeStokes.SmoothSingularCube n m) :
    (smoothIntegralChains m).X n :=
  ∑ σ : Equiv.Perm (Fin n), (Equiv.Perm.sign σ : ℤ) •
    ((Smooth.smoothSingularSubcomplex (Fin m → ℝ)).toSSet.ιChainComplex
      (R := ModuleCat.of ℤ ℤ) (CubicalTriangulation.triangulatedCubeSmoothSimplex cube σ)) 1

/-- The same signed permutation sum in the actual normalized smooth chain group. -/
def normalizedCubeTriangulation (cube : DeRham.Comparison.StokesF.SingularCubeStokes.SmoothSingularCube n m) :
    (normalizedSmoothIntegralChains m).X n :=
  ∑ σ : Equiv.Perm (Fin n), (Equiv.Perm.sign σ : ℤ) •
    ((Smooth.smoothSingularSubcomplex (Fin m → ℝ)).toSSet.ιNormalizedChainComplex
      (R := ModuleCat.of ℤ ℤ) (CubicalTriangulation.triangulatedCubeSmoothSimplex cube σ)) 1

/-- Simplicial normalization carries the genuine signed triangulation to its normalized sum. -/
theorem signedCubeTriangulation_normalize
    (cube : DeRham.Comparison.StokesF.SingularCubeStokes.SmoothSingularCube n m) :
    ((Smooth.smoothSingularSubcomplex (Fin m → ℝ)).toSSet.toNormalizedChainComplex
      (ModuleCat.of ℤ ℤ)).f n (signedCubeTriangulation cube) =
        normalizedCubeTriangulation cube := by
  simp only [signedCubeTriangulation, normalizedCubeTriangulation, map_sum, map_zsmul]
  apply Finset.sum_congr rfl
  intro σ _
  congr 1

/-- Every coordinate-degenerate cube has zero normalized triangulation. -/
theorem normalizedCubeTriangulation_eq_zero_of_degenerate
    (cube : DeRham.Comparison.StokesF.SingularCubeStokes.SmoothSingularCube n m) (hc : DeRham.Comparison.CubicalDegeneracyOperators.IsDegenerateCube cube) :
    normalizedCubeTriangulation cube = 0 := by
  cases n with
  | zero => exact (DeRham.Comparison.CubicalDegeneracyOperators.not_isDegenerate_zero_cube cube hc).elim
  | succ n =>
    unfold normalizedCubeTriangulation
    apply Finset.sum_eq_zero
    intro σ _
    have hz := (Smooth.smoothSingularSubcomplex (Fin m → ℝ)).toSSet.ιNormalizedChainComplex_eq_zero
      (R := ModuleCat.of ℤ ℤ) (CubicalTriangulation.triangulatedCubeSmoothSimplex cube σ)
      (CubicalDegenerate.triangulatedCubeSmoothSimplex_mem_degenerate cube hc σ)
    rw [hz]
    change (Equiv.Perm.sign σ : ℤ) •
      (0 : (normalizedSmoothIntegralChains m).X (n + 1)) = 0
    exact zsmul_zero (Equiv.Perm.sign σ : ℤ)

/-- Integer-linear extension of the normalized signed triangulation to actual cubical chains. -/
def cubicalToNormalizedSimplicialLinear (n m : ℕ) :
    (DeRham.Comparison.StokesF.SingularCubeStokes.SmoothSingularCube n m →₀ ℤ) →ₗ[ℤ]
      (normalizedSmoothIntegralChains m).X n :=
  Finsupp.linearCombination ℤ normalizedCubeTriangulation

/-- The linear extension has the specified value on each cube generator and coefficient. -/
@[simp]
theorem cubicalToNormalizedSimplicialLinear_single
    (cube : DeRham.Comparison.StokesF.SingularCubeStokes.SmoothSingularCube n m) (a : ℤ) :
    cubicalToNormalizedSimplicialLinear n m (Finsupp.single cube a) =
      a • normalizedCubeTriangulation cube := by
  change Finsupp.linearCombination ℤ normalizedCubeTriangulation (Finsupp.single cube a) = _
  exact (Finsupp.linearCombination_single ℤ (v := normalizedCubeTriangulation) a cube).trans
    (int_smul_eq_zsmul
      (inferInstance : Module ℤ ((normalizedSmoothIntegralChains m).X n)) a
      (normalizedCubeTriangulation cube))

/-- The actual cubical degeneracy submodule lies in the kernel of the normalized triangulation. -/
theorem cubicalDegenerateSubmodule_le_triangulationKer (n m : ℕ) :
    DeRham.Comparison.CubicalDegenerateQ.degenerateSubmodule n m ≤ LinearMap.ker (cubicalToNormalizedSimplicialLinear n m) := by
  apply Submodule.span_le.mpr
  rintro _ ⟨cube, hc, rfl⟩
  change cubicalToNormalizedSimplicialLinear n m (Finsupp.single cube 1) = 0
  rw [cubicalToNormalizedSimplicialLinear_single, one_zsmul,
    normalizedCubeTriangulation_eq_zero_of_degenerate cube hc]

/-- The degreewise signed map from normalized cubical chains to actual normalized
smooth simplicial chains. Boundary compatibility is not asserted in this declaration. -/
def normalizedCubicalTriangulation (n m : ℕ) :
    DeRham.Comparison.CubicalDegenerateQ.NormalizedCubicalChain n m →ₗ[ℤ] (normalizedSmoothIntegralChains m).X n :=
  (DeRham.Comparison.CubicalDegenerateQ.degenerateSubmodule n m).liftQ (cubicalToNormalizedSimplicialLinear n m)
    (cubicalDegenerateSubmodule_le_triangulationKer n m)

/-- The quotient map realizes the original signed map on every chain representative. -/
@[simp]
theorem normalizedCubicalTriangulation_mk
    (c : DeRham.Comparison.StokesF.SingularCubeStokes.SmoothSingularCube n m →₀ ℤ) :
    normalizedCubicalTriangulation n m ((DeRham.Comparison.CubicalDegenerateQ.degenerateSubmodule n m).mkQ c) =
      cubicalToNormalizedSimplicialLinear n m c := rfl

/-- In particular the normalized quotient retains the prescribed signed cube sum. -/
@[simp]
theorem normalizedCubicalTriangulation_single
    (cube : DeRham.Comparison.StokesF.SingularCubeStokes.SmoothSingularCube n m) (a : ℤ) :
    normalizedCubicalTriangulation n m
        ((DeRham.Comparison.CubicalDegenerateQ.degenerateSubmodule n m).mkQ (Finsupp.single cube a)) =
      a • normalizedCubeTriangulation cube := by
  rw [normalizedCubicalTriangulation_mk, cubicalToNormalizedSimplicialLinear_single]

/-- The descended degreewise map is characterized uniquely by its values on representatives. -/
theorem normalizedCubicalTriangulation_unique
    (f : DeRham.Comparison.CubicalDegenerateQ.NormalizedCubicalChain n m →ₗ[ℤ] (normalizedSmoothIntegralChains m).X n)
    (hf : f.comp (DeRham.Comparison.CubicalDegenerateQ.degenerateSubmodule n m).mkQ = cubicalToNormalizedSimplicialLinear n m) :
    f = normalizedCubicalTriangulation n m := by
  apply LinearMap.ext
  intro q
  refine Submodule.Quotient.induction_on (DeRham.Comparison.CubicalDegenerateQ.degenerateSubmodule n m) q ?_
  intro c
  exact LinearMap.congr_fun hf c

end

end OAI.AlgebraicTopology.Cohomology.Singular.NormalizedCubicalTriangulation

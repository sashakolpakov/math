import OAI.NumberTheory.PadicHodge.IntegralComparison.Koszul.GeneratorMatrix
import OAI.NumberTheory.PadicHodge.IntegralComparison.Exterior.PowerVanishing

/-! # Top Boundary -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Koszul.TopBoundary

noncomputable section

/-! Evaluation on the top wedge identifies the actual last dual Koszul
boundary with the original ideal of equations. This fixes its orientation. -/

open OAI.AlgebraicGeometry.Crystalline.Cohomology.ExteriorContractionCoe.ExteriorContraction OAI.NumberTheory.PadicHodge.IntegralComparison.TopExteriorCoordinates
  GeneratorMatrix

universe u
variable (R : Type u) [CommRing R]

section TopDual
variable {V : Type u} [AddCommGroup V] [Module R V] {n : ℕ}
  (b : Module.Basis (Fin n) R V)

def topDualEquiv : Module.Dual R (⋀[R]^n V) ≃ₗ[R] R where
  toFun a := a (TopExteriorCoordinates.generator b)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  invFun r := r • TopExteriorCoordinates.coordinate b
  left_inv a := by
    apply LinearMap.ext
    intro x
    change a (TopExteriorCoordinates.generator b) * TopExteriorCoordinates.coordinate b x = a x
    rw [mul_comm, ← smul_eq_mul, ← a.map_smul, TopExteriorCoordinates.reconstruct]
  right_inv r := by simp [TopExteriorCoordinates.coordinate_generator]

@[simp] theorem topDualEquiv_apply (a : Module.Dual R (⋀[R]^n V)) :
    topDualEquiv R b a = a (TopExteriorCoordinates.generator b) := rfl

end TopDual

variable {n : ℕ} (s : Fin (n + 1) → R)

abbrev basis := Pi.basisFun R (Fin (n + 1))

abbrev top := TopExteriorCoordinates.generator (basis R (n := n))

def boundaryValue : Module.Dual R (⋀[R]^n (Fin (n + 1) → R)) →ₗ[R] R where
  toFun a := a (AlgebraicGeometry.Crystalline.Cohomology.ExteriorContractionCoe.ExteriorContraction.contraction R _ (GeneratorMatrix.equation R s) n (top R (n := n)))
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem contraction_sum (x : ⋀[R]^(n + 1) (Fin (n + 1) → R)) :
    AlgebraicGeometry.Crystalline.Cohomology.ExteriorContractionCoe.ExteriorContraction.contraction R _ (GeneratorMatrix.equation R s) n x =
      ∑ i, s i • AlgebraicGeometry.Crystalline.Cohomology.ExteriorContractionCoe.ExteriorContraction.contraction R _ (LinearMap.proj i) n x := by
  apply Subtype.ext
  change CliffordAlgebra.contractLeft (Q := 0) (∑ i, s i • LinearMap.proj i) x.val = _
  simp only [map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply]
  simp only [Submodule.coe_sum, Submodule.coe_smul_of_tower, AlgebraicGeometry.Crystalline.Cohomology.ExteriorContractionCoe.ExteriorContraction.contraction_coe,
    AlgebraicGeometry.Crystalline.Cohomology.ExteriorContractionCoe.ExteriorContraction.ambientContraction]

def coordinateBoundary (i : Fin (n + 1)) :
    Module.Dual R (⋀[R]^n (Fin (n + 1) → R)) :=
  (TopExteriorCoordinates.coordinate (basis R (n := n))).comp (AlgebraicGeometry.Crystalline.Cohomology.ExteriorContractionCoe.ExteriorContraction.wedge R _ (basis R (n := n) i) n)

theorem boundary_coordinate (i : Fin (n + 1)) :
    boundaryValue R s (coordinateBoundary R i) = s i := by
  have hw : AlgebraicGeometry.Crystalline.Cohomology.ExteriorContractionCoe.ExteriorContraction.wedge R _ (basis R (n := n) i) (n + 1) (top R (n := n)) = 0 :=
    Exterior.PowerVanishing.eq_zero (basis R (n := n)) (by omega) _
  have h := AlgebraicGeometry.Crystalline.Cohomology.ExteriorContractionCoe.ExteriorContraction.contraction_wedge R _ (GeneratorMatrix.equation R s) (basis R (n := n) i) n (top R (n := n))
  rw [hw, map_zero, zero_add] at h
  change TopExteriorCoordinates.coordinate (basis R (n := n))
    (AlgebraicGeometry.Crystalline.Cohomology.ExteriorContractionCoe.ExteriorContraction.wedge R _ (basis R (n := n) i) n
      (AlgebraicGeometry.Crystalline.Cohomology.ExteriorContractionCoe.ExteriorContraction.contraction R _ (GeneratorMatrix.equation R s) n (top R (n := n)))) = s i
  rw [h, map_smul, TopExteriorCoordinates.coordinate_generator, smul_eq_mul, mul_one]
  simp [GeneratorMatrix.equation_apply, Pi.basisFun_apply, Pi.single_apply]

theorem boundary_range : (boundaryValue R s).range = Ideal.span (Set.range s) := by
  apply le_antisymm
  · rintro x ⟨a, rfl⟩
    change a (AlgebraicGeometry.Crystalline.Cohomology.ExteriorContractionCoe.ExteriorContraction.contraction R _ (GeneratorMatrix.equation R s) n (top R (n := n))) ∈ Ideal.span (Set.range s)
    rw [contraction_sum, map_sum]
    apply Submodule.sum_mem
    intro i _
    rw [map_smul, smul_eq_mul]
    exact Ideal.mul_mem_right _ _ (Ideal.subset_span (Set.mem_range_self i))
  · apply Ideal.span_le.mpr
    rintro x ⟨i, rfl⟩
    exact ⟨coordinateBoundary R i, boundary_coordinate R s i⟩

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Koszul.TopBoundary

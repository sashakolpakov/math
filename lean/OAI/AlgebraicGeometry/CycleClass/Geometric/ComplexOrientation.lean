import Mathlib.LinearAlgebra.Complex.Orientation
import Mathlib.RingTheory.Complex
import Mathlib.RingTheory.Norm.Transitivity

/-! # Complex Orientation -/

namespace OAI.AlgebraicGeometry.CycleClass.Geometric.ComplexOrientation

noncomputable section

/-!+# Complex orientations of finite-dimensional tangent model spaces

The real determinant of a complex-linear automorphism is the squared complex
norm of its complex determinant and is therefore positive. The real bases
`(v₁, I v₁, …, vₙ, I vₙ)` consequently give one orientation independent of
the chosen complex basis. These are linear-algebraic prerequisites for cycle
orientations; this file does not construct fundamental or cycle classes.
-/

open _root_.Module

variable {V W : Type*}
variable [AddCommGroup V] [Module ℂ V] [Module ℝ V] [IsScalarTower ℝ ℂ V]
variable [AddCommGroup W] [Module ℂ W] [Module ℝ W] [IsScalarTower ℝ ℂ W]

/-- The determinant after restricting a complex-linear map to real scalars. -/
theorem complexLinearMap_realDet (f : V →ₗ[ℂ] V) :
    LinearMap.det (f.restrictScalars ℝ) = Complex.normSq (LinearMap.det f) := by
  rw [LinearMap.det_restrictScalars, Algebra.norm_complex_apply]

/-- Every complex-linear automorphism has positive real determinant. -/
theorem complexLinearEquiv_realDet_pos (e : V ≃ₗ[ℂ] V) :
    0 < LinearMap.det ((e.restrictScalars ℝ).toLinearMap) := by
  change 0 < LinearMap.det (e.toLinearMap.restrictScalars ℝ)
  rw [complexLinearMap_realDet, Complex.normSq_pos]
  exact e.isUnit_det'.ne_zero

variable {ι : Type*}

/-- The real basis obtained from a complex basis by replacing each vector with
itself and its multiple by `I`, in that order. -/
def complexRealBasis (b : Basis ι ℂ V) : Basis (ι × Fin 2) ℝ V :=
  Complex.basisOneI.smulTower' b

@[simp]
theorem complexRealBasis_apply (b : Basis ι ℂ V) (i : ι) (j : Fin 2) :
    complexRealBasis b (i, j) = Complex.basisOneI j • b i := by
  exact Complex.basisOneI.smulTower'_apply b (i, j)

@[simp]
theorem complexRealBasis_map (b : Basis ι ℂ V) (e : V ≃ₗ[ℂ] W) :
    complexRealBasis (b.map e) = (complexRealBasis b).map (e.restrictScalars ℝ) := by
  ext ij
  simp [complexRealBasis, Basis.smulTower'_apply]

variable [Fintype ι] [DecidableEq ι]

/-- The complex orientation as presented by a complex basis. -/
def complexOrientationOfBasis (b : Basis ι ℂ V) : Orientation ℝ V (ι × Fin 2) :=
  (complexRealBasis b).orientation

theorem complexOrientationOfBasis_map (b : Basis ι ℂ V) (e : V ≃ₗ[ℂ] W) :
    complexOrientationOfBasis (b.map e) =
      Orientation.map (ι × Fin 2) (e.restrictScalars ℝ) (complexOrientationOfBasis b) := by
  rw [complexOrientationOfBasis, complexRealBasis_map, Basis.orientation_map]
  rfl

/-- A complex-linear automorphism preserves the orientation of any real basis. -/
theorem complexLinearEquiv_preserves_realBasis_orientation
    {κ : Type*} [Fintype κ] [DecidableEq κ]
    (b : Basis κ ℝ V) (e : V ≃ₗ[ℂ] V) :
    Orientation.map κ (e.restrictScalars ℝ) b.orientation = b.orientation := by
  rw [← Basis.orientation_map]
  exact (b.orientation_comp_linearEquiv_eq_iff_det_pos (e.restrictScalars ℝ)).2
    (complexLinearEquiv_realDet_pos e)

/-- The orientation from the paired real basis is independent of the complex basis. -/
theorem complexOrientationOfBasis_eq (b c : Basis ι ℂ V) :
    complexOrientationOfBasis b = complexOrientationOfBasis c := by
  let e := b.equiv c (Equiv.refl ι)
  have he : b.map e = c := by
    simp [e]
  calc
    complexOrientationOfBasis b =
        Orientation.map (ι × Fin 2) (e.restrictScalars ℝ) (complexOrientationOfBasis b) :=
      (complexLinearEquiv_preserves_realBasis_orientation (complexRealBasis b) e).symm
    _ = complexOrientationOfBasis (b.map e) := (complexOrientationOfBasis_map b e).symm
    _ = complexOrientationOfBasis c := congrArg complexOrientationOfBasis he

/-- Complex-linear coordinate transitions preserve the orientations defined by
any complex bases on the source and target. -/
theorem complexOrientationOfBasis_equiv (b : Basis ι ℂ V) (c : Basis ι ℂ W)
    (e : V ≃ₗ[ℂ] W) :
    Orientation.map (ι × Fin 2) (e.restrictScalars ℝ) (complexOrientationOfBasis b) =
      complexOrientationOfBasis c := by
  rw [← complexOrientationOfBasis_map]
  exact complexOrientationOfBasis_eq (b.map e) c

/-- The standard complex orientation on the real tangent model space `ℂⁿ`. -/
def standardComplexOrientation (n : ℕ) :
    Orientation ℝ (Fin n → ℂ) (Fin n × Fin 2) :=
  complexOrientationOfBasis (Pi.basisFun ℂ (Fin n))

/-- Every complex-linear change of standard complex coordinates preserves
the standard real orientation. -/
theorem standardComplexOrientation_preserved (n : ℕ)
    (e : (Fin n → ℂ) ≃ₗ[ℂ] (Fin n → ℂ)) :
    Orientation.map (Fin n × Fin 2) (e.restrictScalars ℝ)
      (standardComplexOrientation n) = standardComplexOrientation n := by
  exact complexOrientationOfBasis_equiv (Pi.basisFun ℂ (Fin n))
    (Pi.basisFun ℂ (Fin n)) e

end

end OAI.AlgebraicGeometry.CycleClass.Geometric.ComplexOrientation

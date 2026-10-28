import Mathlib.RepresentationTheory.AlgebraRepresentation.Basic
import Mathlib.RingTheory.SimpleModule.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Basic

/-! # Irreducible Density -/

namespace OAI.NumberTheory.Quaternion.Arithmetic.IrreducibleDensity

noncomputable section

/-! Burnside's density conclusion for a finite-dimensional irreducible
algebra representation over an algebraically closed field, using the
existing Schur and Jacobson density theorems. -/

open scoped Classical

theorem irreducible_algebra_action_surjective
    {k R V : Type*} [Field k] [IsAlgClosed k] [Ring R] [Algebra k R]
    [AddCommGroup V] [Module k V] [Module R V] [IsScalarTower k R V]
    [IsSimpleModule R V] [FiniteDimensional k V] :
    Function.Surjective (Module.toModuleEnd k (S := R) V) := by
  intro φ
  let ψ : Module.End (Module.End R V) V :=
    { toFun := φ
      map_add' := φ.map_add
      map_smul' := by
        intro d v
        obtain ⟨a, ha⟩ :=
          (IsSimpleModule.algebraMap_end_bijective_of_isAlgClosed (A := R) (V := V) k).surjective d
        rw [← ha]
        change φ (a • v) = a • φ v
        exact φ.map_smul a v }
  let b := Module.finBasis k V
  obtain ⟨r, hr⟩ := jacobson_density (R := R) ψ (Finset.univ.image b)
  refine ⟨r, ?_⟩
  apply b.ext
  intro i
  exact (hr (b i) (Finset.mem_image.mpr ⟨i, Finset.mem_univ i, rfl⟩)).symm

end

end OAI.NumberTheory.Quaternion.Arithmetic.IrreducibleDensity

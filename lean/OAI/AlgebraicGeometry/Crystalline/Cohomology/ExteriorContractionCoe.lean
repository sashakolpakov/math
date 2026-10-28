import Mathlib.LinearAlgebra.ExteriorPower.Basic
import Mathlib.LinearAlgebra.CliffordAlgebra.Contraction

/-! # Exterior Contraction Coe -/

namespace OAI.AlgebraicGeometry.Crystalline.Cohomology.ExteriorContractionCoe.ExteriorContraction

noncomputable section

/-!
# Exterior multiplication and contraction in each degree

Exterior multiplication raises degree and contraction by a linear
functional lowers degree. These are the signed operators needed to
assemble the coordinate primitives into a cochain homotopy.
-/

universe u

variable (R M : Type u) [CommRing R] [AddCommGroup M] [Module R M]

theorem wedge_mem (v : M) (n : ℕ) {a : ExteriorAlgebra R M} (ha : a ∈ ⋀[R]^n M) :
    ExteriorAlgebra.ι R v * a ∈ ⋀[R]^(n + 1) M := by
  change ExteriorAlgebra.ι R v * a ∈ (LinearMap.range (ExteriorAlgebra.ι R)) ^ (n + 1)
  rw [pow_succ']
  exact Submodule.mul_mem_mul (LinearMap.mem_range_self _ v) ha

def wedge (v : M) (n : ℕ) : (⋀[R]^n M) →ₗ[R] (⋀[R]^(n + 1) M) :=
  ((LinearMap.mulLeft R (ExteriorAlgebra.ι R v)).comp (⋀[R]^n M).subtype).codRestrict
    (⋀[R]^(n + 1) M) (fun a => wedge_mem R M v n a.property)

theorem wedge_coe (v : M) (n : ℕ) (a : ⋀[R]^n M) :
    (wedge R M v n a : ExteriorAlgebra R M) = ExteriorAlgebra.ι R v * (a : ExteriorAlgebra R M) := rfl

theorem wedge_ιMulti (v : M) (n : ℕ) (a : Fin n → M) :
    wedge R M v n (exteriorPower.ιMulti R n a) = exteriorPower.ιMulti R (n + 1) (Fin.cons v a) := by
  apply Subtype.ext
  change ExteriorAlgebra.ι R v * ExteriorAlgebra.ιMulti R n a =
    ExteriorAlgebra.ιMulti R (n + 1) (Fin.cons v a)
  rw [ExteriorAlgebra.ιMulti_succ_apply]
  rfl

theorem wedge_square (v : M) (n : ℕ) (a : ⋀[R]^n M) :
    wedge R M v (n + 1) (wedge R M v n a) = 0 := by
  apply Subtype.ext
  change ExteriorAlgebra.ι R v * (ExteriorAlgebra.ι R v * (a : ExteriorAlgebra R M)) = 0
  rw [← mul_assoc, ExteriorAlgebra.ι_sq_zero, zero_mul]

theorem wedge_anticommute (v w : M) (n : ℕ) (a : ⋀[R]^n M) :
    wedge R M v (n + 1) (wedge R M w n a) +
      wedge R M w (n + 1) (wedge R M v n a) = 0 := by
  apply Subtype.ext
  change ExteriorAlgebra.ι R v * (ExteriorAlgebra.ι R w * (a : ExteriorAlgebra R M)) +
    ExteriorAlgebra.ι R w * (ExteriorAlgebra.ι R v * (a : ExteriorAlgebra R M)) = 0
  rw [← mul_assoc, ← mul_assoc, ← add_mul, ExteriorAlgebra.ι_add_mul_swap, zero_mul]

def ambientContraction (l : Module.Dual R M) : ExteriorAlgebra R M →ₗ[R] ExteriorAlgebra R M :=
  CliffordAlgebra.contractLeft (Q := 0) l

theorem ambientContraction_one (l : Module.Dual R M) : ambientContraction R M l 1 = 0 :=
  CliffordAlgebra.contractLeft_one 0 l

theorem ambientContraction_ι_mul (l : Module.Dual R M) (v : M) (a : ExteriorAlgebra R M) :
    ambientContraction R M l (ExteriorAlgebra.ι R v * a) =
      l v • a - ExteriorAlgebra.ι R v * ambientContraction R M l a :=
  CliffordAlgebra.contractLeft_ι_mul l v a

theorem ambientContraction_degreeZero (l : Module.Dual R M) {a : ExteriorAlgebra R M}
    (ha : a ∈ ⋀[R]^0 M) : ambientContraction R M l a = 0 := by
  have ha' : a ∈ (1 : Submodule R (ExteriorAlgebra R M)) := by
    simpa only [ExteriorAlgebra.exteriorPower, pow_zero] using ha
  obtain ⟨r, rfl⟩ := Submodule.mem_one.mp ha'
  rw [Algebra.algebraMap_eq_smul_one, map_smul, ambientContraction_one, smul_zero]

theorem contraction_generator_mem (l : Module.Dual R M) (n : ℕ) (v : Fin (n + 1) → M) :
    ambientContraction R M l (ExteriorAlgebra.ιMulti R (n + 1) v) ∈ ⋀[R]^n M := by
  induction n with
  | zero =>
    rw [ExteriorAlgebra.ιMulti_succ_apply, ExteriorAlgebra.ιMulti_zero_apply, mul_one]
    have hc : ambientContraction R M l (ExteriorAlgebra.ι R (v 0)) =
        algebraMap R (ExteriorAlgebra R M) (l (v 0)) := CliffordAlgebra.contractLeft_ι 0 l (v 0)
    rw [hc]
    change algebraMap R (ExteriorAlgebra R M) (l (v 0)) ∈ (1 : Submodule R (ExteriorAlgebra R M))
    exact Submodule.mem_one.mpr ⟨l (v 0), rfl⟩
  | succ n ih =>
    rw [ExteriorAlgebra.ιMulti_succ_apply, ambientContraction_ι_mul]
    apply Submodule.sub_mem
    · exact Submodule.smul_mem _ _ (ExteriorAlgebra.ιMulti_range R (n + 1) (Set.mem_range_self _))
    · exact wedge_mem R M (v 0) n (ih (Matrix.vecTail v))

theorem contraction_mem (l : Module.Dual R M) (n : ℕ) {a : ExteriorAlgebra R M}
    (ha : a ∈ ⋀[R]^(n + 1) M) : ambientContraction R M l a ∈ ⋀[R]^n M := by
  have hsub : (⋀[R]^(n + 1) M) ≤ (⋀[R]^n M).comap (ambientContraction R M l) := by
    rw [← exteriorPower.ιMulti_span_fixedDegree R (n + 1) M]
    apply Submodule.span_le.mpr
    rintro _ ⟨v, rfl⟩
    exact contraction_generator_mem R M l n v
  exact hsub ha

def contraction (l : Module.Dual R M) (n : ℕ) : (⋀[R]^(n + 1) M) →ₗ[R] (⋀[R]^n M) :=
  ((ambientContraction R M l).comp (⋀[R]^(n + 1) M).subtype).codRestrict (⋀[R]^n M)
    (fun a => contraction_mem R M l n a.property)

theorem contraction_coe (l : Module.Dual R M) (n : ℕ) (a : ⋀[R]^(n + 1) M) :
    (contraction R M l n a : ExteriorAlgebra R M) = ambientContraction R M l (a : ExteriorAlgebra R M) := rfl

theorem contraction_wedge_zero (l : Module.Dual R M) (v : M) (a : ⋀[R]^0 M) :
    contraction R M l 0 (wedge R M v 0 a) = l v • a := by
  apply Subtype.ext
  change ambientContraction R M l (ExteriorAlgebra.ι R v * (a : ExteriorAlgebra R M)) = l v • _
  rw [ambientContraction_ι_mul, ambientContraction_degreeZero R M l a.property, mul_zero, sub_zero]

/-- The basic signed relation between exterior multiplication and contraction. -/
theorem contraction_wedge (l : Module.Dual R M) (v : M) (n : ℕ) (a : ⋀[R]^(n + 1) M) :
    contraction R M l (n + 1) (wedge R M v (n + 1) a) +
      wedge R M v n (contraction R M l n a) = l v • a := by
  apply Subtype.ext
  change ambientContraction R M l (ExteriorAlgebra.ι R v * (a : ExteriorAlgebra R M)) +
    ExteriorAlgebra.ι R v * ambientContraction R M l (a : ExteriorAlgebra R M) = l v • _
  rw [ambientContraction_ι_mul, sub_add_cancel]

end

end OAI.AlgebraicGeometry.Crystalline.Cohomology.ExteriorContractionCoe.ExteriorContraction

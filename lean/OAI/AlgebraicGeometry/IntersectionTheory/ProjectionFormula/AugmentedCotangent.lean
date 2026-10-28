import Mathlib.RingTheory.Ideal.Cotangent
import Mathlib.LinearAlgebra.Isomorphisms
import Mathlib.LinearAlgebra.Dimension.Constructions

/-! # Augmented Cotangent -/

namespace OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.AugmentedCotangent

noncomputable section

/-! An algebra with a point valued in its coefficient field has a
first-order decomposition into a value and a cotangent vector. -/

universe u v

variable {K : Type u} {R : Type v} [Field K] [CommRing R] [Algebra K R]
  (ε : R →ₐ[K] K)

abbrev ideal : Ideal R := RingHom.ker ε.toRingHom

def center : R →ₗ[K] ideal ε where
  toFun r := ⟨r - algebraMap K R (ε r), by simp⟩
  map_add' r s := by
    apply Subtype.ext
    simp only [map_add, AddMemClass.coe_add]
    ring
  map_smul' c r := by
    apply Subtype.ext
    change c • r - algebraMap K R (ε (c • r)) = c • (r - algebraMap K R (ε r))
    simp [Algebra.smul_def, mul_sub]

def differential : R →ₗ[K] (ideal ε).Cotangent :=
  ((ideal ε).toCotangent.restrictScalars K).comp (center ε)

def jet : R →ₗ[K] K × (ideal ε).Cotangent := ε.toLinearMap.prod (differential ε)

theorem center_constant (c : K) : center ε (algebraMap K R c) = 0 := by
  apply Subtype.ext
  simp [center]

theorem differential_constant (c : K) : differential ε (algebraMap K R c) = 0 := by
  change (ideal ε).toCotangent (center ε (algebraMap K R c)) = 0
  rw [center_constant, map_zero]

theorem center_mem (r : ideal ε) : center ε r.val = r := by
  apply Subtype.ext
  have hr : ε r.val = 0 := r.property
  simp [center, hr]

theorem differential_mem (r : ideal ε) :
    differential ε r.val = (ideal ε).toCotangent r := by
  change (ideal ε).toCotangent (center ε r.val) = _
  rw [center_mem]

theorem jet_surjective : Function.Surjective (jet ε) := by
  rintro ⟨c, v⟩
  obtain ⟨r, rfl⟩ := (ideal ε).toCotangent_surjective v
  refine ⟨algebraMap K R c + r.val, ?_⟩
  apply Prod.ext
  · change ε (algebraMap K R c + r.val) = c
    have hr : ε r.val = 0 := r.property
    simp [hr]
  · change differential ε (algebraMap K R c + r.val) = _
    rw [map_add, differential_constant, differential_mem, zero_add]

theorem jet_ker : (jet ε).ker = ((ideal ε) ^ 2).restrictScalars K := by
  ext r
  constructor
  · intro hr
    have he : ε r = 0 := congrArg Prod.fst hr
    have hd : differential ε r = 0 := congrArg Prod.snd hr
    rw [show differential ε r = (ideal ε).toCotangent ⟨r, he⟩ from differential_mem ε ⟨r, he⟩,
      Ideal.toCotangent_eq_zero] at hd
    exact hd
  · intro hr
    have hm : r ∈ ideal ε := Ideal.pow_le_self (by decide : 2 ≠ 0) hr
    apply Prod.ext
    · exact hm
    · change differential ε r = 0
      rw [differential_mem ε ⟨r, hm⟩, Ideal.toCotangent_eq_zero]
      exact hr

def quotientEquiv : (R ⧸ ((ideal ε) ^ 2).restrictScalars K) ≃ₗ[K] K × (ideal ε).Cotangent :=
  (Submodule.quotEquivOfEq _ _ (jet_ker ε).symm).trans
    ((jet ε).quotKerEquivOfSurjective (jet_surjective ε))

theorem quotient_finrank [Module.Finite K (ideal ε).Cotangent] :
    Module.finrank K (R ⧸ ((ideal ε) ^ 2).restrictScalars K) =
      1 + Module.finrank K (ideal ε).Cotangent := by
  rw [(quotientEquiv ε).finrank_eq, Module.finrank_prod, Module.finrank_self]

end

end OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.AugmentedCotangent

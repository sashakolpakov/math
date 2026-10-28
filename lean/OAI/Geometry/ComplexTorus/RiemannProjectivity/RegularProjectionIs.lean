import OAI.Geometry.ComplexTorus.RiemannProjectivity.GenericProjectionOn
import Mathlib.Analysis.Normed.Ring.Units
import Mathlib.Analysis.Normed.Operator.Banach
import Mathlib.LinearAlgebra.Basis.VectorSpace

/-! # Regular Projection Is -/

namespace OAI.Geometry.ComplexTorus.RiemannProjectivity.RegularProjectionIs.Constructions.RegularProjection

noncomputable section

/-!
# RiemannProjectivity: cone projections with a prescribed regular tangent space

The cone-avoiding matrices are dense. Invertibility on a fixed tangent
space is an open, nonempty condition, so the projection can satisfy both
requirements simultaneously.
-/

open Set _root_.Module
open scoped BigOperators

variable {n k : ℕ}

/-- View columns as the continuous linear operator they define. -/
def matrixOperator : (Fin (n + 1) → Fin k → ℂ) →ₗ[ℂ]
    ((Fin (n + 1) → ℂ) →L[ℂ] (Fin k → ℂ)) :=
  ∑ j : Fin (n + 1),
    ((ContinuousLinearMap.proj j : (Fin (n + 1) → ℂ) →L[ℂ] ℂ).smulRightₗ).comp
      (LinearMap.proj j)

theorem matrixOperator_apply (M : Fin (n + 1) → Fin k → ℂ) (v : Fin (n + 1) → ℂ) :
    matrixOperator M v = ∑ j, v j • M j := by
  simp [matrixOperator, LinearMap.sum_apply]

theorem matrixOperator_columns (L : (Fin (n + 1) → ℂ) →L[ℂ] (Fin k → ℂ)) :
    matrixOperator (fun j => L (Pi.single j 1)) = L := by
  classical
  ext v i
  have heq : ∑ j : Fin (n + 1), v j • Pi.single j (1 : ℂ) = v := by
    ext j
    simp [Finset.sum_apply, Pi.single_apply]
  have h : matrixOperator (fun j => L (Pi.single j 1)) v = L v := by
    rw [matrixOperator_apply]
    simp_rw [← map_smul]
    rw [← map_sum]
    exact congrArg L heq
  exact congrFun h i

theorem isOpen_regular_matrices
    (A : (Fin k → ℂ) →L[ℂ] (Fin (n + 1) → ℂ)) :
    IsOpen {M : Fin (n + 1) → Fin k → ℂ | Function.Bijective ((matrixOperator M).comp A)} := by
  have hc : Continuous (fun M : Fin (n + 1) → Fin k → ℂ => (matrixOperator M).comp A) :=
    matrixOperator.continuous_of_finiteDimensional.clm_comp continuous_const
  simpa only [Set.preimage_ofPred_eq, ContinuousLinearMap.isUnit_iff_bijective] using!
    Units.isOpen.preimage hc

theorem nonempty_regular_matrices
    (A : (Fin k → ℂ) →L[ℂ] (Fin (n + 1) → ℂ)) (hA : Function.Injective A) :
    {M : Fin (n + 1) → Fin k → ℂ | Function.Bijective ((matrixOperator M).comp A)}.Nonempty := by
  obtain ⟨g, hg⟩ := A.toLinearMap.exists_leftInverse_of_injective (LinearMap.ker_eq_bot.mpr hA)
  let L := g.toContinuousLinearMap
  refine ⟨fun j => L (Pi.single j 1), ?_⟩
  change Function.Bijective ((matrixOperator (fun j => L (Pi.single j 1))).comp A)
  rw [matrixOperator_columns]
  have heq : L.comp A = ContinuousLinearMap.id ℂ (Fin k → ℂ) := by
    apply ContinuousLinearMap.ext
    intro v
    exact LinearMap.congr_fun hg v
  rw [heq]
  exact Function.bijective_id

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]
  [NormedSpace ℝ V] [IsScalarTower ℝ ℂ V] [FiniteDimensional ℂ V]

/-- Avoid the entire projective cone while remaining invertible on one
prescribed tangent space of the same dimension as the projection target. -/
theorem exists_regular_projection_avoiding (hk : finrank ℂ V < k)
    (U : Fin (n + 1) → Set V) (r : Fin (n + 1) → V → Fin n → ℂ)
    (hU : ∀ i, IsOpen (U i)) (hr : ∀ i, DifferentiableOn ℂ (r i) (U i))
    (S : Set (Fin (n + 1) → ℂ))
    (hcover : ∀ v ∈ S, v ≠ 0 → ∃ i z, z ∈ U i ∧ v i ≠ 0 ∧
      ∀ j, v (i.succAbove j) / v i = r i z j)
    (A : (Fin k → ℂ) →L[ℂ] (Fin (n + 1) → ℂ)) (hA : Function.Injective A) :
    ∃ L : (Fin (n + 1) → ℂ) →L[ℂ] (Fin k → ℂ),
      (∀ v ∈ S, L v = 0 → v = 0) ∧ Function.Bijective (L.comp A) := by
  obtain ⟨M, hMreg, hM⟩ := (GenericProjectionOn.Constructions.GenericProjection.dense_matrices_avoiding hk U r hU hr).inter_open_nonempty
    _ (isOpen_regular_matrices A) (nonempty_regular_matrices A hA)
  refine ⟨matrixOperator M, ?_, hMreg⟩
  intro v hv hLv
  by_contra hv0
  obtain ⟨i, z, hz, hi, hratio⟩ := hcover v hv hv0
  have hsum : ∑ j, v j • M j = 0 := (matrixOperator_apply M v).symm.trans hLv
  exact hM i z hz (i.removeNth M)
    (GenericProjectionOn.Constructions.GenericProjection.eq_badMatrix_of_annihilates i (r i) z v M hi hratio hsum)

end

end OAI.Geometry.ComplexTorus.RiemannProjectivity.RegularProjectionIs.Constructions.RegularProjection

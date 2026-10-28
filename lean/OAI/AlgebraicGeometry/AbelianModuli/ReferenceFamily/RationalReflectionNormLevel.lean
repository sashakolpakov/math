import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.DenseRationalLatticeReflections
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.MatrixFormScaling

/-! # Rational Reflection Norm Level -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.RationalReflectionNormLevel

noncomputable section

/-! The rational lattice-reflection construction applies to vectors
with any common nonzero norm coming from the original field. In
particular, it applies directly to the native ball lifts of norm μ(b).
-/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {E : Type*} [Field E] [NumberField E] [NumberField.IsCMField E]

theorem exists_rational_lattice_reflections_at_common_norm
    (μ : E →+* ℂ) (H : Matrix (Fin 3) (Fin 3) E)
    (hHerm : ∀ i j, H i j = NumberField.IsCMField.complexConj E (H j i))
    (w : Fin 3 → E)
    (hw : MatrixReflectionEmbedding.matrixReflectionForm (NumberField.IsCMField.complexConj E).toRingHom H w w ≠ 0)
    (Λ : Submodule ℤ (Fin 3 → E)) (hΛ : NumberTheory.ArithmeticGroups.Data.CongruenceLevel.FullStableLattice Λ)
    (N : ℕ) (hN : 0 < N) (q : E) (hq : q ≠ 0)
    (hqσ : NumberField.IsCMField.complexConj E q = q)
    (x y : Fin 3 → ℂ)
    (hx : MatrixReflectionEmbedding.matrixReflectionForm (starRingEnd ℂ) (H.map μ) x x = μ q)
    (hy : MatrixReflectionEmbedding.matrixReflectionForm (starRingEnd ℂ) (H.map μ) y y = μ q)
    (U : Set (Fin 3 → ℂ)) (hU : IsOpen U)
    (hyU : ∀ u : ℂ, ‖u‖ = 1 → u • y ∈ U) :
    ∃ g : (Fin 3 → E) ≃ₗ[E] (Fin 3 → E),
      ((LinearMap.toMatrix' g.toLinearMap).map μ).mulVec x ∈ U ∧
      (∀ a d, MatrixReflectionEmbedding.matrixReflectionForm (NumberField.IsCMField.complexConj E).toRingHom H
        (g a) (g d) =
          MatrixReflectionEmbedding.matrixReflectionForm (NumberField.IsCMField.complexConj E).toRingHom H a d) ∧
      LinearMap.det g.toLinearMap = 1 ∧
      LatticeReflectionCongruence.ClearedPrincipalLatticeCongruence Λ N g := by
  let σ := (NumberField.IsCMField.complexConj E).toRingHom
  let a : E := -q⁻¹
  have ha : a ≠ 0 := neg_ne_zero.mpr (inv_ne_zero hq)
  have haσ : σ a = a := by
    change σ (-q⁻¹) = -q⁻¹
    rw [map_neg, map_inv₀]
    exact congrArg (fun z : E => -z⁻¹) hqσ
  let H' : Matrix (Fin 3) (Fin 3) E := a • H
  have hHerm' : ∀ i j, H' i j = σ (H' j i) := by
    intro i j
    change a * H i j = σ (a * H j i)
    rw [map_mul, haσ]
    exact congrArg (fun z : E => a * z) (hHerm i j)
  have hw' : MatrixReflectionEmbedding.matrixReflectionForm σ H' w w ≠ 0 := by
    rw [show H' = a • H from rfl, MatrixFormScaling.matrixReflectionForm_smul]
    exact ReflectionScaling.hermitian_norm_form_smul_ne_zero σ (MatrixReflectionEmbedding.matrixReflectionForm σ H) a ha w hw
  have haq : μ a * μ q = -1 := by
    have hμq : μ q ≠ 0 := (map_ne_zero μ).mpr hq
    simp [a, map_neg, map_inv₀, hμq]
  have hx' : MatrixReflectionEmbedding.matrixReflectionForm (starRingEnd ℂ) (H'.map μ) x x = -1 := by
    rw [show H' = a • H from rfl, MatrixFormScaling.matrixReflectionForm_map_smul]
    change μ a * MatrixReflectionEmbedding.matrixReflectionForm (starRingEnd ℂ) (H.map μ) x x = -1
    rw [hx, haq]
  have hy' : MatrixReflectionEmbedding.matrixReflectionForm (starRingEnd ℂ) (H'.map μ) y y = -1 := by
    rw [show H' = a • H from rfl, MatrixFormScaling.matrixReflectionForm_map_smul]
    change μ a * MatrixReflectionEmbedding.matrixReflectionForm (starRingEnd ℂ) (H.map μ) y y = -1
    rw [hy, haq]
  obtain ⟨g, hg, hpres, hdet, hcongr⟩ := DenseRationalLatticeReflections.exists_rational_lattice_reflections_in_orbit_neighborhood
    μ H' hHerm' w hw' Λ hΛ N hN x y hx' hy' U hU hyU
  refine ⟨g, hg, ?_, hdet, hcongr⟩
  intro v t
  apply mul_left_cancel₀ ha
  have h := hpres v t
  rw [show H' = a • H from rfl, MatrixFormScaling.matrixReflectionForm_smul] at h
  exact h

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.RationalReflectionNormLevel

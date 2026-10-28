import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.DenseRationalLatticeReflections
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.ComponentUniformization
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Complex.HermitianMatrixForm
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.EmbeddedLinearGroup

/-! # Reflection Interfaces -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.ReflectionInterfaces

noncomputable section

/-! Literal comparisons with the original ReferenceFamily Hermitian expressions
and embedded complex-linear action. The arithmetic density result is
restated on those original objects, with all comparison maps proved.
-/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {E : Type} [Field E] [NumberField E] [Algebra ℚ E] [NumberField.IsCMField E]

omit [Algebra ℚ E] in
theorem matrixReflectionForm_eq_original
    (H : Matrix (Fin 3) (Fin 3) E) (x y : Fin 3 → E) :
    MatrixReflectionEmbedding.matrixReflectionForm (NumberField.IsCMField.complexConj E).toRingHom H x y =
      Datum.RankThreePELDatum.matrixHermitian H x y :=
  MatrixReflectionEmbedding.matrixReflectionForm_apply _ H x y

omit [NumberField E] [Algebra ℚ E] [NumberField.IsCMField E] in
theorem complexReflectionForm_eq_original
    (μ : E →+* ℂ) (H : Matrix (Fin 3) (Fin 3) E) (x y : Fin 3 → ℂ) :
    MatrixReflectionEmbedding.matrixReflectionForm (starRingEnd ℂ) (H.map μ) x y =
      Datum.RankThreePELDatum.complexMatrixHermitian μ H x y :=
  MatrixReflectionEmbedding.matrixReflectionForm_apply _ (H.map μ) x y

theorem complexReflectionForm_eq_bundled (H : Matrix (Fin 3) (Fin 3) ℂ) :
    MatrixReflectionEmbedding.matrixReflectionForm (starRingEnd ℂ) H = Complex.HermitianMatrixForm.complexHermitianMatrixForm H := rfl

omit [NumberField E] [NumberField.IsCMField E] in
theorem reflection_matrix_action_eq_original
    (μ : E →ₐ[ℚ] ℂ) (g : (Fin 3 → E) ≃ₗ[E] (Fin 3 → E)) (x : Fin 3 → ℂ) :
    ((LinearMap.toMatrix' g.toLinearMap).map μ.toRingHom).mulVec x =
      EmbeddedLinearGroup.embeddedLinearIso g μ x := rfl

theorem exists_original_rational_lattice_reflections_in_orbit_neighborhood
    (μ : E →ₐ[ℚ] ℂ) (H : Matrix (Fin 3) (Fin 3) E)
    (hHerm : ∀ i j, H i j = NumberField.IsCMField.complexConj E (H j i))
    (w : Fin 3 → E) (hw : Datum.RankThreePELDatum.matrixHermitian H w w ≠ 0)
    (Λ : Submodule ℤ (Fin 3 → E)) (hΛ : NumberTheory.ArithmeticGroups.Data.CongruenceLevel.FullStableLattice Λ)
    (N : ℕ) (hN : 0 < N) (x y : Fin 3 → ℂ)
    (hx : Datum.RankThreePELDatum.complexMatrixHermitian μ.toRingHom H x x = -1)
    (hy : Datum.RankThreePELDatum.complexMatrixHermitian μ.toRingHom H y y = -1)
    (U : Set (Fin 3 → ℂ)) (hU : IsOpen U)
    (hyU : ∀ u : ℂ, ‖u‖ = 1 → u • y ∈ U) :
    ∃ g : (Fin 3 → E) ≃ₗ[E] (Fin 3 → E),
      EmbeddedLinearGroup.embeddedLinearIso g μ x ∈ U ∧
      (∀ a d, Datum.RankThreePELDatum.matrixHermitian H (g a) (g d) =
        Datum.RankThreePELDatum.matrixHermitian H a d) ∧
      LinearMap.det g.toLinearMap = 1 ∧
      LatticeReflectionCongruence.ClearedPrincipalLatticeCongruence Λ N g := by
  have hw' : MatrixReflectionEmbedding.matrixReflectionForm (NumberField.IsCMField.complexConj E).toRingHom H w w ≠ 0 := by
    rwa [matrixReflectionForm_eq_original]
  have hx' : MatrixReflectionEmbedding.matrixReflectionForm (starRingEnd ℂ) (H.map μ.toRingHom) x x = -1 := by
    rwa [complexReflectionForm_eq_original]
  have hy' : MatrixReflectionEmbedding.matrixReflectionForm (starRingEnd ℂ) (H.map μ.toRingHom) y y = -1 := by
    rwa [complexReflectionForm_eq_original]
  have hΛ' : @NumberTheory.ArithmeticGroups.Data.CongruenceLevel.FullStableLattice E _ DivisionRing.toRatAlgebra Λ := by
    have hA : (inferInstance : Algebra ℚ E) = DivisionRing.toRatAlgebra := Subsingleton.elim _ _
    exact hA ▸ hΛ
  obtain ⟨g, hg, hpres, hdet, hcongr⟩ := DenseRationalLatticeReflections.exists_rational_lattice_reflections_in_orbit_neighborhood
    μ.toRingHom H hHerm w hw' Λ hΛ' N hN x y hx' hy' U hU hyU
  refine ⟨g, ?_, ?_, hdet, hcongr⟩
  · rwa [reflection_matrix_action_eq_original] at hg
  · intro a d
    simpa only [matrixReflectionForm_eq_original] using hpres a d

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.ReflectionInterfaces

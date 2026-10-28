import OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.Finite.CoefficientPadic
import OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.AdelicTensorDensity
import OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.CoefficientVectorCoordinates
import OAI.RepresentationTheory.Hecke.RadialDilation.SplitScalarCoordinates

/-! # Split Coordinates -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.SplitCoordinates.TestTransport

noncomputable section

section

/-! Completed PEL vectors and all their split q-adic evaluations have
the same coordinates in any retained rational basis. -/

open scoped Classical TensorProduct

open OAI.RepresentationTheory.Hecke.RadialDilation.SplitScalarCoordinates.Realization

variable (E : Type) [Field E] [NumberField E] [IsGalois ℚ E]
  (K : Type*) [NontriviallyNormedField K] [Algebra ℚ K]
  [Algebra E K] [IsScalarTower ℚ E K]
  {S J : Type*} [Fintype S] [DecidableEq S] [Fintype J] [DecidableEq J]
  (σ : S ≃ (E →ₐ[ℚ] K)) (e : (Fin 3 → E) ≃ₗ[ℚ] (J → ℚ))

def splitLabelCoordinates : (S → Fin 3 → K) ≃ₗ[K] (J → K) :=
  ({ toFun := fun y τ => y (σ.symm τ)
     invFun := fun y v => y (σ v)
     left_inv := fun y => by funext v; exact congrArg y (σ.symm_apply_apply v)
     right_inv := fun y => by funext τ; exact congrArg y (σ.apply_symm_apply τ)
     map_add' := fun _ _ => rfl
     map_smul' := fun _ _ => rfl } :
    (S → Fin 3 → K) ≃ₗ[K] ((E →ₐ[ℚ] K) → Fin 3 → K)).trans
      (RepresentationTheory.Hecke.RadialDilation.SplitScalarCoordinates.Realization.splitRationalCoordinates E (K) e)

variable [CompleteSpace K]

omit [DecidableEq S] in
theorem splitLabelCoordinates_continuous : Continuous (splitLabelCoordinates E K σ e) :=
  (splitLabelCoordinates E K σ e).toLinearMap.continuous_of_finiteDimensional

omit [Fintype S] [DecidableEq S] [CompleteSpace K] in
theorem splitLabelCoordinates_rational (x : Fin 3 → E) :
    splitLabelCoordinates E K σ e (fun v i => σ v (x i)) =
      fun j => algebraMap ℚ (K) (e x j) := by
  have h := RepresentationTheory.Hecke.RadialDilation.SplitScalarCoordinates.Realization.splitRationalCoordinates_tmul E (K) e 1 x
  rw [RepresentationTheory.Hecke.RadialDilation.Complexification.Realization.splitRankThreeBaseChange_tmul_eq, one_smul, one_smul] at h
  change RepresentationTheory.Hecke.RadialDilation.SplitScalarCoordinates.Realization.splitRationalCoordinates E (K) e (fun τ i => σ (σ.symm τ) (x i)) = _
  simpa only [Equiv.apply_symm_apply] using h

omit [DecidableEq S] in
theorem coefficientVectorCoordinates_split (f : AbelianModuli.ReferenceFamily.AdelicData.RationalFiniteAdeles →ₐ[ℚ] K)
    (hf : Continuous f) (x : Fin 3 → AbelianModuli.ReferenceFamily.AdelicData.FiniteCoefficients E) :
    splitLabelCoordinates E K σ e (fun v i => TensorEvaluation.TestTransport.tensorEvaluation f (σ v) (x i)) =
      fun j => f (CoefficientVectorCoordinates.TestTransport.coefficientVectorCoordinates E e x j) := by
  have hd : DenseRange (fun y : Fin 3 → E => fun i => AbelianModuli.ReferenceFamily.AdelicData.finiteCoefficientEmbedding E (y i)) :=
    DenseRange.piMap (fun _ => AdelicTensorDensity.TestTransport.denseRange_finiteCoefficientEmbedding E)
  have he : (fun x : Fin 3 → AbelianModuli.ReferenceFamily.AdelicData.FiniteCoefficients E =>
      splitLabelCoordinates E K σ e (fun v i => TensorEvaluation.TestTransport.tensorEvaluation f (σ v) (x i))) =
      (fun x : Fin 3 → AbelianModuli.ReferenceFamily.AdelicData.FiniteCoefficients E =>
        fun j => f (CoefficientVectorCoordinates.TestTransport.coefficientVectorCoordinates E e x j)) := by
    apply hd.equalizer
      ((splitLabelCoordinates_continuous E K σ e).comp (continuous_pi (fun v => continuous_pi
        (fun i => (Finite.CoefficientEvaluation.TestTransport.finiteCoefficientEvaluation_continuous E f (σ v) hf).comp (continuous_apply i)))))
      (continuous_pi (fun j => hf.comp
        ((continuous_apply j).comp (CoefficientVectorCoordinates.TestTransport.coefficientVectorHomeomorph E e).continuous)))
    funext y
    dsimp only [Function.comp_apply]
    have hrat (v : S) (a : E) : TensorEvaluation.TestTransport.tensorEvaluation f (σ v) (AbelianModuli.ReferenceFamily.AdelicData.finiteCoefficientEmbedding E a) = σ v a :=
      (TensorEvaluation.TestTransport.tensorEvaluation_tmul f (σ v) 1 a).trans (by rw [map_one, one_mul])
    simp only [hrat]
    change splitLabelCoordinates E K σ e (fun v i => σ v (y i)) =
      (fun j => f (CoefficientVectorCoordinates.TestTransport.coefficientVectorCoordinates E e
        (fun i => AbelianModuli.ReferenceFamily.AdelicData.finiteCoefficientEmbedding E (y i)) j))
    rw [splitLabelCoordinates_rational, CoefficientVectorCoordinates.TestTransport.coefficientVectorCoordinates_rational]
    funext j
    exact (f).commutes (e y j) |>.symm
  exact congr_fun he x

end

/-! Identity labels leave the retained split rational coordinates unchanged. -/

open scoped Classical

open OAI.RepresentationTheory.Hecke.RadialDilation.SplitScalarCoordinates.Realization

variable (E : Type) [Field E] [NumberField E] [IsGalois ℚ E]
  (K : Type*) [NontriviallyNormedField K] [Algebra ℚ K]
  [Algebra E K] [IsScalarTower ℚ E K]
  {J : Type*} [Fintype J] [DecidableEq J]

theorem splitLabelCoordinates_refl (e : (Fin 3 → E) ≃ₗ[ℚ] (J → ℚ))
    (x : (E →ₐ[ℚ] K) → Fin 3 → K) :
    splitLabelCoordinates E K (Equiv.refl (E →ₐ[ℚ] K)) e x = RepresentationTheory.Hecke.RadialDilation.SplitScalarCoordinates.Realization.splitRationalCoordinates E K e x := rfl

end

end OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.SplitCoordinates.TestTransport

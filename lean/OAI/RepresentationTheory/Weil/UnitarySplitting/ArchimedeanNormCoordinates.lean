import OAI.RepresentationTheory.Weil.UnitarySplitting.ArchimedeanBase
import OAI.RepresentationTheory.Weil.UnitarySplitting.QuadraticNorm

/-! # Archimedean Norm Coordinates -/

namespace OAI.RepresentationTheory.Weil.UnitarySplitting.ArchimedeanNormCoordinates.Construction

noncomputable section

/-! A quadratic extension of a real local field has complex coordinates,
and its algebraic norm is the squared complex absolute value. -/

theorem complex_coordinates_for_quadratic_extension
    {F E : Type} [NormedField F] [NormedField E] [Algebra F E]
    [FiniteDimensional F E]
    (e : ℝ ≃+* F) (he : Continuous e)
    (hEmbedding : Continuous (algebraMap F E)) (hQuadratic : Module.finrank F E = 2) :
    ∃ k : E ≃+* ℂ, Continuous k ∧ Continuous k.symm ∧
      (∀ a : F, k (algebraMap F E a) = (e.symm a : ℂ)) ∧
      ∀ x : E, e.symm (Algebra.norm F x) = Complex.normSq (k x) := by
  let : Algebra ℝ F := e.toRingHom.toAlgebra
  let ef : ℝ ≃ₐ[ℝ] F := { e with commutes' := fun _ => rfl }
  let : FiniteDimensional ℝ F := ef.toLinearEquiv.finiteDimensional
  let : Algebra ℝ E := ((algebraMap F E).comp e.toRingHom).toAlgebra
  let : IsScalarTower ℝ F E := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  let : FiniteDimensional ℝ E := FiniteDimensional.trans ℝ F E
  let : ContinuousSMul ℝ E := continuousSMul_of_algebraMap ℝ E (hEmbedding.comp he)
  have hdimF : Module.finrank ℝ F = 1 := ef.toLinearEquiv.finrank_eq.symm.trans (Module.finrank_self ℝ)
  have hdimE : Module.finrank ℝ E = 2 := by
    rw [← Module.finrank_mul_finrank ℝ F E, hdimF, hQuadratic, one_mul]
  let j : E →ₐ[ℝ] ℂ := IsAlgClosed.lift
  have hsurj : Function.Surjective j :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
      (f := j.toLinearMap) (hdimE.trans Complex.finrank_real_complex.symm)).mp j.injective
  let k := AlgEquiv.ofBijective j ⟨j.injective, hsurj⟩
  refine ⟨k.toRingEquiv, k.toLinearEquiv.toContinuousLinearEquiv.continuous,
    k.toLinearEquiv.toContinuousLinearEquiv.symm.continuous, ?_, ?_⟩
  · intro a
    change k (algebraMap F E a) = (e.symm a : ℂ)
    have hh := k.commutes (e.symm a)
    change k (algebraMap F E (e (e.symm a))) = (e.symm a : ℂ) at hh
    simpa only [e.apply_symm_apply] using hh
  · intro x
    have hbase := Algebra.norm_eq_of_ringEquiv e (show (algebraMap F E).comp e.toRingHom =
      algebraMap ℝ E from rfl) x
    have hk := Algebra.norm_eq_of_algEquiv k x
    rw [Algebra.norm_complex_eq] at hk
    rw [← hbase, e.symm_apply_apply]
    exact hk.symm

end

end OAI.RepresentationTheory.Weil.UnitarySplitting.ArchimedeanNormCoordinates.Construction

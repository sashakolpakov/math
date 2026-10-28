import OAI.RepresentationTheory.Weil.UnitarySplitting.LocalTest

/-! # Archimedean Base -/

namespace OAI.RepresentationTheory.Weil.UnitarySplitting.ArchimedeanBase.Construction

noncomputable section

/-! An archimedean base field with a quadratic field extension is real.
The dimension argument embeds the tower into the algebraically closed
field of complex numbers; no local-field classification is assumed. -/

theorem real_equiv_of_unbounded_with_quadratic_extension
    {F E : Type} [NormedField F] [Field E] [Algebra F E]
    [CompleteSpace F] [LocallyCompactSpace F] [CharZero F] [FiniteDimensional F E]
    (h : ¬ ∀ n : ℕ, ‖(n : F)‖ ≤ 1) (hQuadratic : Module.finrank F E = 2) :
    ∃ e : ℝ ≃+* F, Continuous e ∧ Continuous e.symm := by
  let j := LocalTest.Construction.realEmbeddingOfUnbounded F h
  let : Algebra ℝ F := j.toAlgebra
  let : ContinuousSMul ℝ F := continuousSMul_of_algebraMap ℝ F
    (LocalTest.Construction.realEmbeddingOfUnbounded_continuous F h)
  let : FiniteDimensional ℝ F := FiniteDimensional.of_locallyCompactSpace ℝ
  let : Algebra ℝ E := ((algebraMap F E).comp j).toAlgebra
  let : IsScalarTower ℝ F E := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  let : FiniteDimensional ℝ E := FiniteDimensional.trans ℝ F E
  let k : E →ₐ[ℝ] ℂ := IsAlgClosed.lift
  have hle : Module.finrank ℝ E ≤ 2 := by
    have hh := LinearMap.finrank_le_finrank_of_injective (f := k.toLinearMap) k.injective
    simpa using hh
  have hmul := Module.finrank_mul_finrank ℝ F E
  rw [hQuadratic] at hmul
  have hpos : 0 < Module.finrank ℝ F := Module.finrank_pos
  have hdim : Module.finrank ℝ F = 1 := by omega
  have hbij : Function.Bijective (algebraMap ℝ F) :=
    Algebra.finrank_eq_one_iff_bijective_algebraMap.mp hdim
  let e : ℝ ≃ₐ[ℝ] F := AlgEquiv.ofBijective (Algebra.ofId ℝ F) hbij
  refine ⟨e.toRingEquiv, ?_, ?_⟩
  · exact e.toLinearEquiv.toContinuousLinearEquiv.continuous
  · exact e.toLinearEquiv.toContinuousLinearEquiv.symm.continuous

end

end OAI.RepresentationTheory.Weil.UnitarySplitting.ArchimedeanBase.Construction

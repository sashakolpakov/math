import OAI.AlgebraicGeometry.ComplexMultiplication.WeightOne

/-! # Transport -/

namespace OAI.AlgebraicGeometry.ComplexMultiplication

noncomputable section

/-! Transport rational weight-one Hodge structures along rational linear
equivalences, respecting the actual coefficient conjugation. -/

variable {U V : Type*} [AddCommGroup U] [Module ℚ U] [AddCommGroup V] [Module ℚ V]
  (H : WeightOne.CM.WeightOneHodgeStructure U) (e : U ≃ₗ[ℚ] V)

/-- Transport changes only rational coordinates. Its conjugation condition
is proved using naturality of the actual coefficient conjugation. -/
def WeightOne.CM.WeightOneHodgeStructure.transport : WeightOne.CM.WeightOneHodgeStructure V where
  finiteDimensional := by
    let : Module.Finite ℚ U := H.finiteDimensional
    exact Module.Finite.of_surjective e.toLinearMap e.surjective
  holomorphic := H.holomorphic.map (e.baseChange ℚ ℂ _ _).toLinearMap
  antiholomorphic := H.antiholomorphic.map (e.baseChange ℚ ℂ _ _).toLinearMap
  complementary := (Submodule.orderIsoMapComap (e.baseChange ℚ ℂ _ _)).isCompl_iff.mp
    H.complementary
  conjugate_mem := by
    intro y
    let ec := e.baseChange ℚ ℂ _ _
    obtain ⟨x, rfl⟩ := ec.surjective y
    have hc : WeightOne.CM.coefficientConjugation V (ec x) = ec (WeightOne.CM.coefficientConjugation U x) :=
      (WeightOne.CM.baseChange_coefficientConjugation e.toLinearMap x).symm
    rw [hc, Submodule.mem_map_equiv, Submodule.mem_map_equiv]
    simpa only [ec, LinearEquiv.symm_apply_apply] using H.conjugate_mem x

theorem WeightOne.CM.WeightOneHodgeStructure.transport_holomorphic (x : WeightOne.CM.Complexification U) :
    (e.baseChange ℚ ℂ _ _) x ∈ (H.transport e).holomorphic ↔ x ∈ H.holomorphic := by
  change (e.baseChange ℚ ℂ _ _) x ∈ H.holomorphic.map
    (e.baseChange ℚ ℂ _ _).toLinearMap ↔ x ∈ H.holomorphic
  rw [Submodule.mem_map_equiv, LinearEquiv.symm_apply_apply]

theorem WeightOne.CM.WeightOneHodgeStructure.transport_antiholomorphic (x : WeightOne.CM.Complexification U) :
    (e.baseChange ℚ ℂ _ _) x ∈ (H.transport e).antiholomorphic ↔ x ∈ H.antiholomorphic := by
  change (e.baseChange ℚ ℂ _ _) x ∈ H.antiholomorphic.map
    (e.baseChange ℚ ℂ _ _).toLinearMap ↔ x ∈ H.antiholomorphic
  rw [Submodule.mem_map_equiv, LinearEquiv.symm_apply_apply]

theorem WeightOne.CM.WeightOneHodgeStructure.transport_isHodgeMap : WeightOne.CM.IsHodgeMap H (H.transport e) e.toLinearMap := by
  intro x hx
  exact (H.transport_holomorphic e x).mpr hx

theorem WeightOne.CM.WeightOneHodgeStructure.transport_symm_isHodgeMap : WeightOne.CM.IsHodgeMap (H.transport e) H e.symm.toLinearMap := by
  intro x hx
  change x ∈ H.holomorphic.map (e.baseChange ℚ ℂ _ _).toLinearMap at hx
  rw [Submodule.mem_map_equiv] at hx
  exact hx

end

end OAI.AlgebraicGeometry.ComplexMultiplication

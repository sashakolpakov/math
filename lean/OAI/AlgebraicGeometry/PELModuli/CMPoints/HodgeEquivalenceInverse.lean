import OAI.AlgebraicGeometry.ComplexMultiplication.Hodge.Transport

/-! # Hodge Equivalence Inverse -/

namespace OAI.AlgebraicGeometry.PELModuli.CMPoints.HodgeEquivalenceInverse

noncomputable section

/-! A bijective rational Hodge map has a Hodge inverse: the two
complementary types and coefficient conjugation force the inverse type. -/

theorem inverse_isHodgeMap_of_equiv
    {U V : Type*} [AddCommGroup U] [Module ℚ U] [AddCommGroup V] [Module ℚ V]
    (H : ComplexMultiplication.WeightOne.CM.WeightOneHodgeStructure U) (J : ComplexMultiplication.WeightOne.CM.WeightOneHodgeStructure V)
    (e : U ≃ₗ[ℚ] V) (h : ComplexMultiplication.WeightOne.CM.IsHodgeMap H J e.toLinearMap) :
    ComplexMultiplication.WeightOne.CM.IsHodgeMap J H e.symm.toLinearMap := by
  let C := H.transport e
  have hhol : C.holomorphic ≤ J.holomorphic := by
    rintro _ ⟨x, hx, rfl⟩
    exact h x hx
  have hanti : C.antiholomorphic ≤ J.antiholomorphic := by
    rintro _ ⟨x, hx, rfl⟩
    exact h.map_antiholomorphic hx
  have hback : J.holomorphic ≤ C.holomorphic := by
    intro x hx
    have hall : x ∈ C.holomorphic ⊔ C.antiholomorphic := by
      rw [C.complementary.sup_eq_top]
      exact Submodule.mem_top
    obtain ⟨u, hu, v, hv, huv⟩ := Submodule.mem_sup.mp hall
    have hvhol : v ∈ J.holomorphic := by
      have he : v = x - u := by rw [← huv]; abel
      rw [he]
      exact J.holomorphic.sub_mem hx (hhol hu)
    have hvzero : v = 0 := Submodule.disjoint_def.mp J.complementary.disjoint v hvhol (hanti hv)
    rw [hvzero, add_zero] at huv
    exact huv ▸ hu
  intro x hx
  exact H.transport_symm_isHodgeMap e x (hback hx)

end

end OAI.AlgebraicGeometry.PELModuli.CMPoints.HodgeEquivalenceInverse

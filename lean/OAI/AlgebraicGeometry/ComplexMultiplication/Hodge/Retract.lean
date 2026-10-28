import OAI.AlgebraicGeometry.ComplexMultiplication.Decomposition

/-! # Retract -/

namespace OAI.AlgebraicGeometry.ComplexMultiplication.Hodge.Retract

noncomputable section

/-! # Hodge structures on rational retracts

A rational projection preserving Hodge type gives the actual induced Hodge
structure on its image. No algebraic-cycle assertion is used.
-/

open scoped TensorProduct

open OAI.AlgebraicGeometry.ComplexMultiplication.Decomposition.CM

variable {U : Type*} [AddCommGroup U] [Module ℚ U]

/-- The complexified retraction is still a left inverse of the actual inclusion. -/
theorem baseChange_retract (S : Submodule ℚ U) (r : U →ₗ[ℚ] S)
    (hr : r.comp S.subtype = LinearMap.id) (x : WeightOne.CM.Complexification S) :
    r.baseChange ℂ (S.subtype.baseChange ℂ x) = x := by
  change (r.baseChange ℂ ∘ₗ S.subtype.baseChange ℂ) x = x
  rw [← LinearMap.baseChange_comp, hr, LinearMap.baseChange_id]
  rfl

/-- A Hodge projection induces complementary Hodge subspaces on its rational image. -/
def hodgeRetract (H : WeightOne.CM.WeightOneHodgeStructure U) (S : Submodule ℚ U)
    (r : U →ₗ[ℚ] S) (hr : r.comp S.subtype = LinearMap.id)
    (hP : WeightOne.CM.IsHodgeMap H H (S.subtype.comp r)) : WeightOne.CM.WeightOneHodgeStructure S := by
  letI : FiniteDimensional ℚ U := H.finiteDimensional
  let j := S.subtype.baseChange ℂ
  let t := r.baseChange ℂ
  have htj (x : WeightOne.CM.Complexification S) : t (j x) = x := baseChange_retract S r hr x
  have hji : Function.Injective j := Function.LeftInverse.injective htj
  have hjt (x : WeightOne.CM.Complexification U) : j (t x) = (S.subtype.comp r).baseChange ℂ x := by
    rw [LinearMap.baseChange_comp]
    rfl
  refine
    { holomorphic := H.holomorphic.comap j
      antiholomorphic := H.antiholomorphic.comap j
      complementary := ?_
      conjugate_mem := ?_ }
  · constructor
    · apply Submodule.disjoint_def.mpr
      intro x hx ha
      apply hji
      exact (Submodule.disjoint_def.mp H.complementary.disjoint (j x) hx ha).trans j.map_zero.symm
    · apply codisjoint_iff.mpr
      apply top_unique
      intro x _
      obtain ⟨a, ha, b, hb, hab⟩ := Submodule.mem_sup.mp
        (show j x ∈ H.holomorphic ⊔ H.antiholomorphic from
          H.complementary.sup_eq_top.symm ▸ Submodule.mem_top)
      apply Submodule.mem_sup.mpr
      refine ⟨t a, ?_, t b, ?_, ?_⟩
      · change j (t a) ∈ H.holomorphic
        rw [hjt]
        exact hP a ha
      · change j (t b) ∈ H.antiholomorphic
        rw [hjt]
        exact hP.map_antiholomorphic hb
      · exact (t.map_add a b).symm.trans ((congrArg t hab).trans (htj x))
  · intro x
    change j (WeightOne.CM.coefficientConjugation S x) ∈ H.antiholomorphic ↔ j x ∈ H.holomorphic
    rw [WeightOne.CM.baseChange_coefficientConjugation]
    exact H.conjugate_mem (j x)

/-- The rational inclusion preserves the induced Hodge type. -/
theorem hodgeRetract_inclusion (H : WeightOne.CM.WeightOneHodgeStructure U) (S : Submodule ℚ U)
    (r : U →ₗ[ℚ] S) (hr : r.comp S.subtype = LinearMap.id)
    (hP : WeightOne.CM.IsHodgeMap H H (S.subtype.comp r)) :
    WeightOne.CM.IsHodgeMap (hodgeRetract H S r hr hP) H S.subtype := by
  intro x hx
  exact hx

end

end OAI.AlgebraicGeometry.ComplexMultiplication.Hodge.Retract

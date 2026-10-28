import OAI.AlgebraicGeometry.PELModuli.IntegralModel.TorsionDivision

/-! # Generator Criterion -/

namespace OAI.AlgebraicGeometry.PELModuli.IntegralModel.CM

noncomputable section

/-! A finite geometric criterion for a primitive endomorphism to extend to
the entire integral CM action. The full action is constructed from the
minimal-polynomial equation and the torsion restrictions of the fixed
integral reconstruction polynomials. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.Polynomial

variable {E : Type} [Field E] [NumberField E] [Algebra ℚ E] [NumberField.IsCMField E]
  (D : GeneratorReconstruction.CMIntegralGeneratorData E) {S : Scheme} {g : ℕ} (A : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g S)

def GeneratorReconstruction.CMIntegralGeneratorData.GeneratorConditions (u : Finite.Actions.GroupEndRing A) : Prop :=
  aeval u (minpoly ℤ (D.generator : E)) = 0 ∧
    ∀ i : Fin (Module.finrank ℤ (NumberField.RingOfIntegers E)),
      A.torsionInclusion D.conductor ≫
        (aeval u (D.polynomial (Finite.Actions.integralActionBasis E i))).hom A = 1

theorem GeneratorReconstruction.CMIntegralGeneratorData.generator_conditions_of_action
    (ρ : AbelianModuli.ReferenceFamily.ActionData.IntegralAction (NumberField.RingOfIntegers E) A) :
    D.GeneratorConditions A ((Finite.Actions.ringHomOfIntegralAction A ρ) D.generator) := by
  let r := Finite.Actions.ringHomOfIntegralAction A ρ
  constructor
  · have h := aeval_algHom_apply r.toIntAlgHom D.generator
      (minpoly ℤ (D.generator : E))
    rw [NumberField.RingOfIntegers.minpoly_coe, minpoly.aeval, map_zero] at h
    rw [NumberField.RingOfIntegers.minpoly_coe]
    exact h
  · intro i
    apply TorsionDivision.torsion_zero_of_division A D.conductor _ (r (Finite.Actions.integralActionBasis E i))
    have h := aeval_algHom_apply r.toIntAlgHom D.generator
      (D.polynomial (Finite.Actions.integralActionBasis E i))
    rw [D.integral_reconstruction, map_mul, map_natCast] at h
    exact h.symm

theorem GeneratorReconstruction.CMIntegralGeneratorData.existsUnique_integral_action_of_generator_conditions
    (u : Finite.Actions.GroupEndRing A)
    (hc : ∀ s : S, IsUnit (D.conductor : S.presheaf.stalk s))
    (hu : D.GeneratorConditions A u) :
    ∃! ρ : AbelianModuli.ReferenceFamily.ActionData.IntegralAction (NumberField.RingOfIntegers E) A,
      ρ.map D.generator = u.hom A := by
  classical
  choose v hv using fun i =>
    (TorsionDivision.existsUnique_groupEnd_division A D.conductor hc
      (aeval u (D.polynomial (Finite.Actions.integralActionBasis E i))) (hu.2 i)).exists
  obtain ⟨r, hr, _⟩ := D.existsUnique_ring_action_of_basis_division u hu.1
    (Finite.Actions.GroupEndRing.unit_natCast_mul_injective A D.conductor hc) (Finite.Actions.integralActionBasis E) v hv
  let ρ := Finite.Actions.integralActionOfRingHom A r
  have hρ : ρ.map D.generator = u.hom A := congrArg (Finite.Actions.GroupEndRing.hom A) hr
  refine ⟨ρ, hρ, fun σ hσ => ?_⟩
  exact D.integral_action_eq_of_generator A σ ρ hc (hσ.trans hρ.symm)

theorem GeneratorReconstruction.CMIntegralGeneratorData.generator_conditions_iff_exists_action
    (u : Finite.Actions.GroupEndRing A)
    (hc : ∀ s : S, IsUnit (D.conductor : S.presheaf.stalk s)) :
    D.GeneratorConditions A u ↔
      ∃ ρ : AbelianModuli.ReferenceFamily.ActionData.IntegralAction (NumberField.RingOfIntegers E) A,
        ρ.map D.generator = u.hom A := by
  constructor
  · intro hu
    exact (D.existsUnique_integral_action_of_generator_conditions A u hc hu).exists
  · rintro ⟨ρ, hρ⟩
    have hr : (Finite.Actions.ringHomOfIntegralAction A ρ) D.generator = u := Finite.Actions.GroupEndRing.ext A hρ
    exact hr ▸ D.generator_conditions_of_action A ρ

end

end OAI.AlgebraicGeometry.PELModuli.IntegralModel.CM

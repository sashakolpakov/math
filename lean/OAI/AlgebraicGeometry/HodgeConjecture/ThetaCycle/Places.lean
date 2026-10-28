import OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.Cm

/-! # Places -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.Places.CM

noncomputable section

/-! Select one representative of every conjugate pair, using any prescribed
odd CM type that is positive at the identity. This supplies the finite places
and the distinguished identity required by the concrete theta construction. -/

open scoped Classical
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.GeometricSource.CM

variable (K : IntermediateField ℚ ℂ)
  [NumberField K] [NumberField.IsCMField K]
  (v : ComplexMultiplication.OddSignSwitch.CM.OddSignPattern (fun g : Gal(K/ℚ) => ComplexMultiplication.GaloisSigns.CM.CMCoefficientField.conjugation K * g))

theorem positive_type_pair_bijective : Function.Bijective
    (fun p : {g : Gal(K/ℚ) // v.val g = true} × Bool =>
      if p.2 then ComplexMultiplication.GaloisSigns.CM.CMCoefficientField.conjugation K * p.1.val else p.1.val) := by
  constructor
  · rintro ⟨⟨a, ha⟩, p⟩ ⟨⟨b, hb⟩, q⟩ he
    cases p <;> cases q
    · exact Prod.ext (Subtype.ext he) rfl
    · have hs := congrArg v.val he
      change v.val a = v.val (ComplexMultiplication.GaloisSigns.CM.CMCoefficientField.conjugation K * b) at hs
      rw [ha, v.property b, hb] at hs
      cases hs
    · have hs := congrArg v.val he
      change v.val (ComplexMultiplication.GaloisSigns.CM.CMCoefficientField.conjugation K * a) = v.val b at hs
      rw [v.property a, ha, hb] at hs
      cases hs
    · exact Prod.ext (Subtype.ext (mul_left_cancel he)) rfl
  · intro g
    by_cases hg : v.val g = true
    · exact ⟨(⟨g, hg⟩, false), rfl⟩
    · have hc : v.val (ComplexMultiplication.GaloisSigns.CM.CMCoefficientField.conjugation K * g) = true := by
        rw [v.property g, Bool.eq_false_of_not_eq_true hg]
        rfl
      exact ⟨(⟨ComplexMultiplication.GaloisSigns.CM.CMCoefficientField.conjugation K * g, hc⟩, true), ComplexMultiplication.ExteriorSignReduction.CM.CMCoefficientField.conjugation_mul_involutive K g⟩

def placesFromType (hv : v.val 1 = true) : HeckeCycles.GeometricSource.CM.Places K := by
  let I := {g : Gal(K/ℚ) // v.val g = true}
  let e : I ≃ Fin (Fintype.card I) := Fintype.equivFin I
  refine ⟨Fintype.card I, fun i => (e.symm i).val, e ⟨1, hv⟩, ?_, ?_⟩
  · exact congrArg Subtype.val (e.symm_apply_apply ⟨1, hv⟩)
  · exact (positive_type_pair_bijective K v).comp
      (Equiv.prodCongr e.symm (Equiv.refl Bool)).bijective

theorem placesFromType_positive (hv : v.val 1 = true)
    (i : Fin (placesFromType K v hv).count) :
    v.val ((placesFromType K v hv).representative i) = true :=
  ((Fintype.equivFin {g : Gal(K/ℚ) // v.val g = true}).symm i).property

end

end OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.Places.CM

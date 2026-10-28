import OAI.AlgebraicGeometry.AbelianScheme.CentralAction.Arithmetic

/-! # Ideal Conjugation -/

namespace OAI.AlgebraicGeometry.AbelianScheme.CentralAction.IdealConjugation.Construction

noncomputable section

/-! The fractional-ideal conjugation in the arithmetic proof agrees with
the ordinary map of integral ideals by CM conjugation. -/

open _root_.NumberField
open scoped nonZeroDivisors

variable {E : Type*} [Field E] [NumberField E] [IsCMField E]

theorem fraction_conjugation_eq :
    IsFractionRing.ringEquivOfRingEquiv (K := E) (L := E)
        (IsCMField.ringOfIntegersComplexConj E).toRingEquiv =
      (IsCMField.complexConj E).toRingEquiv := by
  apply RingEquiv.toRingHom_injective
  apply IsLocalization.ringHom_ext (𝓞 E)⁰
  ext b
  exact IsFractionRing.ringEquivOfRingEquiv_algebraMap
    (IsCMField.ringOfIntegersComplexConj E).toRingEquiv b

theorem mem_conjugateIdeal (I : Arithmetic.Construction.FI E) (x : E) :
    x ∈ Arithmetic.Construction.conjugateIdeal I ↔ IsCMField.complexConj E x ∈ I := by
  rw [Arithmetic.Construction.conjugateIdeal, FractionalIdeal.ringEquivOfRingEquiv_apply]
  change (∃ y, y ∈ I ∧
    IsFractionRing.ringEquivOfRingEquiv (K := E) (L := E)
      (IsCMField.ringOfIntegersComplexConj E).toRingEquiv y = x) ↔ _
  simp only [fraction_conjugation_eq]
  constructor
  · rintro ⟨y, hy, rfl⟩
    change IsCMField.complexConj E (IsCMField.complexConj E y) ∈ I
    rw [IsCMField.complexConj_apply_apply]
    exact hy
  · intro hx
    exact ⟨IsCMField.complexConj E x, hx, IsCMField.complexConj_apply_apply E x⟩

theorem conjugateIdeal_coe (I : Ideal (𝓞 E)) :
    Arithmetic.Construction.conjugateIdeal (I : Arithmetic.Construction.FI E) =
      ((I.map (IsCMField.ringOfIntegersComplexConj E).toRingHom) : Arithmetic.Construction.FI E) := by
  ext x
  rw [mem_conjugateIdeal, FractionalIdeal.mem_coeIdeal, FractionalIdeal.mem_coeIdeal]
  constructor
  · rintro ⟨a, ha, he⟩
    refine ⟨IsCMField.ringOfIntegersComplexConj E a,
      Ideal.mem_map_of_mem _ ha, ?_⟩
    change IsCMField.complexConj E (a : E) = x
    change (a : E) = IsCMField.complexConj E x at he
    rw [he, IsCMField.complexConj_apply_apply]
  · rintro ⟨b, hb, he⟩
    obtain ⟨a, ha, hab⟩ :=
      (Ideal.mem_map_of_equiv (IsCMField.ringOfIntegersComplexConj E).toRingEquiv b).mp hb
    refine ⟨a, ha, ?_⟩
    change (a : E) = IsCMField.complexConj E x
    change (b : E) = x at he
    rw [← he, ← hab]
    exact (IsCMField.complexConj_apply_apply E (a : E)).symm

end

end OAI.AlgebraicGeometry.AbelianScheme.CentralAction.IdealConjugation.Construction

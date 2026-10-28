import OAI.RepresentationTheory.Theta.Adelic.QuadraticNormCharacter

/-! # Quadratic Norm Transport -/

namespace OAI.RepresentationTheory.Theta.Adelic.QuadraticNormTransport

noncomputable section

/-! Transport the actual norm criterion through a field equivalence,
using the coefficientwise equivalence of the quadratic algebras. -/

open OAI.RepresentationTheory.Theta.Adelic.QuadraticNormSquareQuotient OAI.RepresentationTheory.Theta.Adelic.QuadraticNormCharacter

variable {k l : Type*} [Field k] [Field l]

def quadraticEquiv (e : k ≃+* l) (d : k) : Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic k d ≃+* Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic l (e d) :=
  { Weil.AdelicSplitting.UnitaryBase.Construction.quadraticBaseChange e.toRingHom d with
    invFun := fun z => ⟨e.symm z.re, e.symm z.im⟩
    left_inv := fun z => by ext <;> simp [Weil.AdelicSplitting.UnitaryBase.Construction.quadraticBaseChange]
    right_inv := fun z => by ext <;> simp [Weil.AdelicSplitting.UnitaryBase.Construction.quadraticBaseChange] }

theorem normUnits_map (e : k ≃+* l) (d : k) (b : (Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic k d)ˣ) :
    QuadraticNormSquareQuotient.normUnits (e d) (Units.map (quadraticEquiv e d).toMonoidHom b) =
      Units.map e.toMonoidHom (QuadraticNormSquareQuotient.normUnits d b) := by
  apply Units.ext
  exact Weil.AdelicSplitting.UnitaryBase.Construction.quadraticBaseChange_norm e.toRingHom d b.val

theorem normRange_map_iff (e : k ≃+* l) (d : k) (a : kˣ) :
    Units.map e.toMonoidHom a ∈ (QuadraticNormSquareQuotient.normUnits (e d)).range ↔ a ∈ (QuadraticNormSquareQuotient.normUnits d).range := by
  constructor
  · rintro ⟨b, hb⟩
    let b' := Units.map (quadraticEquiv e d).symm.toMonoidHom b
    refine ⟨b', ?_⟩
    have he := normUnits_map e d b'
    have hbb : Units.map (quadraticEquiv e d).toMonoidHom b' = b := by
      apply Units.ext
      exact (quadraticEquiv e d).apply_symm_apply b.val
    rw [hbb, hb] at he
    apply Units.ext
    exact e.injective (congrArg Units.val he.symm)
  · rintro ⟨b, rfl⟩
    exact ⟨Units.map (quadraticEquiv e d).toMonoidHom b, normUnits_map e d b⟩

theorem normSign_map (e : k ≃+* l) (d : k) (a : kˣ) :
    QuadraticNormCharacter.normSign (e d) (Units.map e.toMonoidHom a) = QuadraticNormCharacter.normSign d a := by
  unfold QuadraticNormCharacter.normSign
  rw [normRange_map_iff]

end

end OAI.RepresentationTheory.Theta.Adelic.QuadraticNormTransport

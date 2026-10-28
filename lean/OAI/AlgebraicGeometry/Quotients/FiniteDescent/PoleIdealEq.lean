import OAI.AlgebraicGeometry.Quotients.FiniteDescent.InverseIdealEq
import OAI.AlgebraicGeometry.Quotients.FiniteDescent.DenominatorIdealEq

/-! # Pole Ideal Eq -/

namespace OAI.AlgebraicGeometry.Quotients.FiniteDescent.PoleIdealEq.Construction.PoleIdeal

/-! A rational function has no pole exactly when its denominator ideal is the unit ideal. -/

variable {R F : Type*} [CommRing R] [Field F] [Algebra R F]

theorem denominator_eq_top (r : F) :
    DenominatorIdealEq.Construction.DenominatorIdeal.ideal (R := R) r = ⊤ ↔ ∃ a : R, algebraMap R F a = r := by
  constructor
  · intro h
    have hm : (1 : R) ∈ DenominatorIdealEq.Construction.DenominatorIdeal.ideal r := by rw [h]; trivial
    obtain ⟨a, ha⟩ := (DenominatorIdealEq.Construction.DenominatorIdeal.mem_iff r (1 : R)).mp hm
    exact ⟨a, by simpa only [map_one, one_mul] using ha.symm⟩
  · rintro ⟨a, rfl⟩
    apply top_unique
    intro b _
    exact ⟨b * a, (map_mul _ b a).symm⟩

theorem inverse_top :
    InverseIdealEq.Construction.InverseIdeal.module (F := F) (⊤ : Ideal R) = Submodule.span R {(1 : F)} := by
  have h := InverseIdealEq.Construction.InverseIdeal.span_eq (R := R) (F := F) 1 (by simp)
  simpa using h

end OAI.AlgebraicGeometry.Quotients.FiniteDescent.PoleIdealEq.Construction.PoleIdeal

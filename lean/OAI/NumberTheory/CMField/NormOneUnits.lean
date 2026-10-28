import Mathlib.NumberTheory.NumberField.CMField
import Mathlib.Tactic.Linarith

/-! # Norm One Units -/

namespace OAI.NumberTheory.CMField.NormOneUnits

/-!
NormOneUnits: an integral unit of a CM field with relative norm one is a root
of unity. We use Mathlib's characterization of torsion units by their
values at infinite places. No project statement stubs are imported.
-/

open scoped _root_.NumberField

/-- Every norm-one unit in the ring of integers of a CM field is a root of unity. -/
theorem norm_one_unit_is_root_of_unity
    {E : Type*} [Field E] [NumberField E]
    [NumberField.IsCMField E]
    (u : (𝓞 E)ˣ)
    (h_norm_one :
      ((u : 𝓞 E) : E) *
        NumberField.IsCMField.complexConj E ((u : 𝓞 E) : E) = 1) :
    ∃ n : ℕ, 0 < n ∧ u ^ n = 1 := by
  have h_torsion : u ∈ NumberField.Units.torsion E := by
    apply (NumberField.Units.mem_torsion E).mpr
    intro w
    have h_square := congrArg w h_norm_one
    rw [map_mul, NumberField.IsCMField.infinitePlace_complexConj, map_one] at h_square
    have h_pos := NumberField.Units.pos_at_place u w
    nlinarith
  exact isOfFinOrder_iff_pow_eq_one.mp ((CommGroup.mem_torsion u).mp h_torsion)

end OAI.NumberTheory.CMField.NormOneUnits

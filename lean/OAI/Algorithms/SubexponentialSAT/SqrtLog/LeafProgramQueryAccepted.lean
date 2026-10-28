import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgramQueryInput

namespace OAI.Algorithms

/-! The accepted (unmarked) query uses the same immutable source masters and
explicitly writes the two false singleton fields consumed by the frontend. -/
namespace SubexponentialSAT.SqrtLog.LeafProgram.Query
open SubexponentialSAT BitProgram StructuredCalls
attribute [local simp] Fin.coe_ofNat_eq_mod

theorem accepted_ready (q : LeafQueryFrontend.Query) (a : Data)
    (hc : CleanWork a) (hs : Sources q a) (hm : q.mark=none) (hi : q.index=[false]) :
    q.Ready (unmarkedInput a) := by
  have e705 := hc 705 (by decide) (by decide)
  have e706 := hc 706 (by decide) (by decide)
  refine ⟨?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · exact (unmarkedInput_frame a 700 (by decide) (by decide)).trans hs.formula
  · exact (unmarkedInput_frame a 701 (by decide) (by decide)).trans hs.rows
  · rw [hi]
    exact unmarkedInput_index a e705
  · simpa only [hm,Option.isSome_none] using unmarkedInput_flag a e706
  · exact (unmarkedInput_frame a 707 (by decide) (by decide)).trans hs.modulus
  · exact (unmarkedInput_frame a 708 (by decide) (by decide)).trans hs.width
  · exact (unmarkedInput_frame a 709 (by decide) (by decide)).trans hs.ambient
  · intro i hlo hhi
    rw [unmarkedInput_frame a i
      (by intro h; have hh := congrArg Fin.val h; norm_num at hh; omega)
      (by intro h; have hh := congrArg Fin.val h; norm_num at hh; omega)]
    exact cleanWork_private a hc i hlo hhi
  · exact (unmarkedInput_frame a 338 (by decide) (by decide)).trans
      (hc 338 (by decide) (by decide))
  · exact (unmarkedInput_frame a 718 (by decide) (by decide)).trans
      (hc 718 (by decide) (by decide))
  · exact (unmarkedInput_frame a 719 (by decide) (by decide)).trans
      (hc 719 (by decide) (by decide))

theorem accepted_outputs_empty (a : Data) (hc : CleanWork a) :
    LeafParametersProgram.Exports.OutputEmpty (unmarkedInput a) ∧
      (unmarkedInput a).stacks 704=[] ∧ (unmarkedInput a).stacks 134=[] ∧
      (unmarkedInput a).stacks 141=[] := by
  constructor
  · intro i
    have hne : ¬Protected (LeafParametersProgram.Exports.destination i) := by fin_cases i <;> decide
    have h321 : LeafParametersProgram.Exports.destination i≠321 := by fin_cases i <;> decide
    rw [unmarkedInput_frame a _ (by fin_cases i <;> decide) (by fin_cases i <;> decide)]
    exact hc _ hne h321
  · refine ⟨?_,?_,?_⟩
    · exact (unmarkedInput_frame a 704 (by decide) (by decide)).trans
        (hc 704 (by decide) (by decide))
    · exact (unmarkedInput_frame a 134 (by decide) (by decide)).trans
        (hc 134 (by decide) (by decide))
    · exact (unmarkedInput_frame a 141 (by decide) (by decide)).trans
        (hc 141 (by decide) (by decide))

end SubexponentialSAT.SqrtLog.LeafProgram.Query

end OAI.Algorithms

import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgramQueryReplay
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgramQueryInput

namespace OAI.Algorithms

/-! The caller's arbitrary source320 and mass322 are absent from the initial
width. Every other live input is a literal immutable query source or reference. -/
namespace SubexponentialSAT.SqrtLog.LeafProgram.Query.Carried
open SubexponentialSAT BitProgram StructuredCalls ProgramTapeReplay

def sourceBytes (a : Data) : ℕ :=
  (a.stacks 700).length+(a.stacks 701).length+(a.stacks 707).length+
    (a.stacks 708).length+(a.stacks 709).length+(a.stacks 321).length

theorem sourceBytes_reference (a : Data) : sourceBytes (reference a)=sourceBytes a := by
  unfold sourceBytes
  rw [reference_visible a 700 (by decide),reference_visible a 701 (by decide),
    reference_visible a 707 (by decide),reference_visible a 708 (by decide),
    reference_visible a 709 (by decide),reference_visible a 321 (by decide)]

theorem reference_clean (a : Data) (hc : CleanWork a) : CleanWork (reference a) := by
  intro i hp hi
  have hh : ¬hidden i := fun hh => hp (hidden_protected i hh)
  exact (reference_visible a i hh).trans (hc i hp hi)

theorem source_width (a : Data) (hc : CleanWork a) (h323 : a.stacks 323=[])
    (hhigh : ∀i : Fin 768,744 ≤ i.val → a.stacks i=[]) :
    ∀i,((reference a).stacks i).length ≤ sourceBytes a := by
  apply reference_width
  intro i hh
  by_cases h321 : i=321
  · subst i
    unfold sourceBytes
    omega
  by_cases hp : Protected i
  · rcases hp with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|hi
    · exact False.elim (hh (by decide))
    · exact False.elim (hh (by decide))
    · simp [h323]
    · unfold sourceBytes; omega
    · unfold sourceBytes; omega
    · unfold sourceBytes; omega
    · unfold sourceBytes; omega
    · unfold sourceBytes; omega
    · simp [hhigh i hi]
  · simp [hc i hp h321]

theorem marked_source_width (a : Data) (hc : CleanWork a) (h323 : a.stacks 323=[])
    (hhigh : ∀i : Fin 768,744 ≤ i.val → a.stacks i=[]) :
    ∀i,((markedInput (reference a)).stacks i).length ≤
      sourceBytes a+10*(a.stacks 321).length+10 := by
  have hc' := reference_clean a hc
  have he := markInput_eval (reference a) (hc' 698 (by decide) (by decide))
    (hc' 699 (by decide) (by decide))
  have hw := eval_width he (sourceBytes a) (source_width a hc h323 hhigh)
  intro i
  have hi := hw i
  rw [reference_visible a 321 (by decide)] at hi
  omega

theorem accepted_source_width (a : Data) (hc : CleanWork a) (h323 : a.stacks 323=[])
    (hhigh : ∀i : Fin 768,744 ≤ i.val → a.stacks i=[]) :
    ∀i,((unmarkedInput (reference a)).stacks i).length ≤ sourceBytes a+3 :=
  eval_width (noMarkInput_eval (reference a)) (sourceBytes a) (source_width a hc h323 hhigh)

end SubexponentialSAT.SqrtLog.LeafProgram.Query.Carried

end OAI.Algorithms

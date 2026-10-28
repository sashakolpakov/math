import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgramQueryInitialWidth
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgramQueryConstruct
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgramQueryEntry

namespace OAI.Algorithms

/-! Obtain the actual arithmetic/layout preparation from immutable raw query
masters. The initial width charges only source bytes and the marked reference. -/
namespace SubexponentialSAT.SqrtLog.LeafProgram.Query.Carried
open SubexponentialSAT BitProgram StructuredCalls LeafParametersProgram

theorem sources_reference (q : LeafQueryFrontend.Query) (a : Data) (hs : Sources q a) :
    Sources q (reference a) := by
  constructor
  · exact (reference_visible a 700 (by decide)).trans hs.formula
  · exact (reference_visible a 701 (by decide)).trans hs.rows
  · exact (reference_visible a 707 (by decide)).trans hs.modulus
  · exact (reference_visible a 708 (by decide)).trans hs.width
  · exact (reference_visible a 709 (by decide)).trans hs.ambient

def markedWidth (a : Data) : ℕ := sourceBytes a+10*(a.stacks 321).length+10
def acceptedWidth (a : Data) : ℕ := sourceBytes a+3

theorem marked_construct (q : LeafQueryFrontend.Query) (k : ℕ) (a : Data)
    (hv : q.Valid) (hg : Guard (q.input k)) (hc : CleanWork a) (hs : Sources q a)
    (hm : q.mark.isSome=true) (href : a.stacks 321=q.index.reverse)
    (h323 : a.stacks 323=[]) (hhigh : ∀i : Fin 768,744 ≤ i.val → a.stacks i=[]) :
    ∃V L, ∃p : Preparation q k (markedInput (reference a)) hg (markedWidth a) V L,
      V=modelValueCap (Circuit.result Serialization.code (Execute.guardedModel (q.input k) p.lengths)) ∧
      L=modelLengthCap (Circuit.result Serialization.code (Execute.guardedModel (q.input k) p.lengths)) := by
  have hc' := reference_clean a hc
  have hr' := (reference_visible a 321 (by decide)).trans href
  obtain ⟨he,hr,ho,hsp⟩ := marked_entry q (reference a) hc' (sources_reference q a hs) hm hr'
  have h728 : (markedInput (reference a)).stacks 728=[] :=
    (markedInput_frame (reference a) 728 (by decide) (by decide) (by decide)).trans
      (hc' 728 (by decide) (by decide))
  exact construct q k _ hv hr ho hsp hg h728 (markedWidth a)
    (marked_source_width a hc h323 hhigh)

theorem accepted_construct (q : LeafQueryFrontend.Query) (k : ℕ) (a : Data)
    (hv : q.Valid) (hg : Guard (q.input k)) (hc : CleanWork a) (hs : Sources q a)
    (hm : q.mark=none) (hindex : q.index=[false])
    (h323 : a.stacks 323=[]) (hhigh : ∀i : Fin 768,744 ≤ i.val → a.stacks i=[]) :
    ∃V L, ∃p : Preparation q k (unmarkedInput (reference a)) hg (acceptedWidth a) V L,
      V=modelValueCap (Circuit.result Serialization.code (Execute.guardedModel (q.input k) p.lengths)) ∧
      L=modelLengthCap (Circuit.result Serialization.code (Execute.guardedModel (q.input k) p.lengths)) := by
  have hc' := reference_clean a hc
  obtain ⟨he,hr,ho,hsp⟩ := accepted_entry q (reference a) hc' (sources_reference q a hs) hm hindex
  have h728 : (unmarkedInput (reference a)).stacks 728=[] :=
    (unmarkedInput_frame (reference a) 728 (by decide) (by decide)).trans
      (hc' 728 (by decide) (by decide))
  exact construct q k _ hv hr ho hsp hg h728 (acceptedWidth a)
    (accepted_source_width a hc h323 hhigh)

end SubexponentialSAT.SqrtLog.LeafProgram.Query.Carried

end OAI.Algorithms

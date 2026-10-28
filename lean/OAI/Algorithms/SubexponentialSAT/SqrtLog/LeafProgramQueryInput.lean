import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgramQueryReference
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafQueryFrontendCore
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafParametersProgramExports

namespace OAI.Algorithms

/-! Concrete source masters and reusable empty workspace at each marked
query boundary. The frontend's hypotheses follow after the paid reference
staging program; no serialized scope or arithmetic cache is an input. -/
namespace SubexponentialSAT.SqrtLog.LeafProgram.Query
open SubexponentialSAT BitProgram StructuredCalls
attribute [local simp] Fin.coe_ofNat_eq_mod

def CleanWork (a : Data) : Prop :=
  ∀i,¬Protected i → i≠321 → a.stacks i=[]

structure Sources (q : LeafQueryFrontend.Query) (a : Data) : Prop where
  formula : a.stacks 700=Encoding.encodeList id q.clauses
  rows : a.stacks 701=HashScopeProgram.RawTable.inputBits q.width.length q.rows
  modulus : a.stacks 707=q.modulus
  width : a.stacks 708=q.width
  ambient : a.stacks 709=q.ambient

theorem cleaned_cleanWork (a : Data) : CleanWork (cleaned a) :=
  fun i hi _ => cleaned_empty a i hi

theorem cleaned_sources (q : LeafQueryFrontend.Query) (a : Data) (h : Sources q a) :
    Sources q (cleaned a) := by
  constructor
  · exact (cleaned_frame a 700 (by decide)).trans h.formula
  · exact (cleaned_frame a 701 (by decide)).trans h.rows
  · exact (cleaned_frame a 707 (by decide)).trans h.modulus
  · exact (cleaned_frame a 708 (by decide)).trans h.width
  · exact (cleaned_frame a 709 (by decide)).trans h.ambient

theorem cleanWork_private (a : Data) (h : CleanWork a) (i : Fin 768)
    (hlo : 340 ≤ i.val) (hhi : i.val < 680) : a.stacks i=[] := by
  apply h
  · intro hp
    simp only [Protected,Fin.ext_iff,Fin.coe_ofNat_eq_mod] at hp
    norm_num at hp
    omega
  · intro hi
    subst i
    norm_num at hlo

theorem marked_ready (q : LeafQueryFrontend.Query) (a : Data)
    (hc : CleanWork a) (hs : Sources q a) (hm : q.mark.isSome=true)
    (href : a.stacks 321=q.index.reverse) : q.Ready (markedInput a) := by
  have e699 := hc 699 (by decide) (by decide)
  have e705 := hc 705 (by decide) (by decide)
  have e706 := hc 706 (by decide) (by decide)
  refine ⟨?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · exact (markedInput_frame a 700 (by decide) (by decide) (by decide)).trans hs.formula
  · exact (markedInput_frame a 701 (by decide) (by decide) (by decide)).trans hs.rows
  · simpa only [href,List.reverse_reverse] using markedInput_index a e699 e705
  · simpa only [hm] using markedInput_flag a e706
  · exact (markedInput_frame a 707 (by decide) (by decide) (by decide)).trans hs.modulus
  · exact (markedInput_frame a 708 (by decide) (by decide) (by decide)).trans hs.width
  · exact (markedInput_frame a 709 (by decide) (by decide) (by decide)).trans hs.ambient
  · intro i hlo hhi
    have hn (x : ℕ) (hx : 680 ≤ x) : i.val≠x := by omega
    rw [markedInput_frame a i
      (by intro h; have hh := congrArg Fin.val h; norm_num at hh; omega)
      (by intro h; have hh := congrArg Fin.val h; norm_num at hh; omega)
      (by intro h; have hh := congrArg Fin.val h; norm_num at hh; omega)]
    exact cleanWork_private a hc i hlo hhi
  · exact (markedInput_frame a 338 (by decide) (by decide) (by decide)).trans
      (hc 338 (by decide) (by decide))
  · exact (markedInput_frame a 718 (by decide) (by decide) (by decide)).trans
      (hc 718 (by decide) (by decide))
  · exact (markedInput_frame a 719 (by decide) (by decide) (by decide)).trans
      (hc 719 (by decide) (by decide))

theorem marked_outputs_empty (a : Data) (hc : CleanWork a) :
    LeafParametersProgram.Exports.OutputEmpty (markedInput a) ∧
      (markedInput a).stacks 704=[] ∧ (markedInput a).stacks 134=[] ∧
      (markedInput a).stacks 141=[] := by
  constructor
  · intro i
    have hne : ¬Protected (LeafParametersProgram.Exports.destination i) := by fin_cases i <;> decide
    have h321 : LeafParametersProgram.Exports.destination i≠321 := by fin_cases i <;> decide
    rw [markedInput_frame a _ (by fin_cases i <;> decide)
      (by fin_cases i <;> decide) (by fin_cases i <;> decide)]
    exact hc _ hne h321
  · refine ⟨?_,?_,?_⟩
    · exact (markedInput_frame a 704 (by decide) (by decide) (by decide)).trans
        (hc 704 (by decide) (by decide))
    · exact (markedInput_frame a 134 (by decide) (by decide) (by decide)).trans
        (hc 134 (by decide) (by decide))
    · exact (markedInput_frame a 141 (by decide) (by decide) (by decide)).trans
        (hc 141 (by decide) (by decide))

end SubexponentialSAT.SqrtLog.LeafProgram.Query

end OAI.Algorithms

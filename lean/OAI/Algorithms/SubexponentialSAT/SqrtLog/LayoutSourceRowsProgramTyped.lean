import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutSourceRowsProgramBounds
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutSourceRowsProgramSemantics

namespace OAI.Algorithms

/-! The paid owner-fiber scan emits the actual compiler bytes of one typed
sum expression. No precomputed polynomial values enter the executable. -/
namespace SubexponentialSAT.SqrtLog.LayoutSourceRowsProgram
open SubexponentialSAT BitProgram StructuredCalls

def TypedSourceRel {C A : Type*} [Add A] [Mul A]
    (encode : C → List Bool) (decode : C → A) (value : ℕ → A) (L : ℕ)
    (i : ℕ) (e : Algorithm.Expr C) : Prop :=
  (e.map decode).eval=value i ∧
    (SubexpPostfixControl.serializeCode encode e.compile).length ≤ L

theorem sourceForOwner_typed {C A : Type*} [AddMonoid A] [Mul A]
    (encode : C → List Bool) (decode : C → A) (value : ℕ → A)
    (z : C) (hz : encode z=[]) (hzero : decode z=0)
    (source : Code) (base : Store) (I K L : ℕ)
    (spec : RelSourceSpec source base
      (fun e : Algorithm.Expr C => SubexpPostfixControl.serializeCode encode e.compile)
      (TypedSourceRel encode decode value L) I K L)
    (query : ℕ) (ps : List (ℕ × ℕ))
    (hq : base 320=LayoutOwnerFiberProgram.unary query)
    (hs : base 337=LayoutOwnerFiberProgram.stream ps)
    (hclean : ∀ i : Fin 11, 2 ≤ i.val → base (ownerStacks i)=[])
    (h305 : base 305=[]) (h287 : base 287=[]) (h333 : base 333=[])
    (hI : ∀ i∈LayoutOwnerFiberProgram.fiberIndices query 0 ps, i ≤ I)
    (regs : Fin 16 → Bool) :
    ∃ e : Algorithm.Expr C, ∃ n rf,
      (e.map decode).eval=ownerSum ps query value ∧
      (SubexpPostfixControl.serializeCode encode e.compile).length ≤
        2+(LayoutOwnerFiberProgram.fiberIndices query 0 ps).length*(L+2) ∧
      n ≤ LayoutOwnerFiberProgram.budget query ps+
        (LayoutOwnerFiberProgram.fiberIndices query 0 ps).length*(K+5*I+3*L+15)+6 ∧
      Eval (sourceForOwner source) n (⟨regs,base⟩ : Data)
        (⟨rf,Function.update base 333
          (SubexpPostfixControl.serializeCode encode e.compile).reverse⟩ : Data) := by
  obtain ⟨ws,n,rf,hr,hn,he⟩ := sourceForOwner_run source base _
    (TypedSourceRel encode decode value L) I K L spec query ps hq hs hclean
    h305 h287 h333 hI regs
  refine ⟨foldSources (.lit z) ws,n,rf,?_,?_,hn,?_⟩
  · rw [foldSources_map_eval]
    have hmean : List.Forall₂ (fun i e => (e.map decode).eval=value i)
        (LayoutOwnerFiberProgram.fiberIndices query 0 ps) ws := by
      exact List.Forall₂.imp (fun _ _ h => h.1) hr
    rw [related_sources_sum decode value _ ws hmean]
    simp [Algorithm.Expr.map,Algorithm.Expr.eval,hzero,ownerSum]
  · exact fullSource_length_le encode (TypedSourceRel encode decode value L) L
      (fun _ _ h => h.2) _ ws hr z hz
  · simpa only [foldSources_zero_code encode z hz ws] using he

end SubexponentialSAT.SqrtLog.LayoutSourceRowsProgram

end OAI.Algorithms

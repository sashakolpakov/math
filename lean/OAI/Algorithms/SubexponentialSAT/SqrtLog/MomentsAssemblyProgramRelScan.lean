import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.MomentsAssemblyProgramRelModel

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.MomentsAssembly.Relational
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls
variable {A W : Type*}

def BodyContract (src : Fin 768) (body : Code) (encode : W → List Bool)
    (step : A → W → A → Prop) (bound : ℕ)
    (inv : A → (Fin 768 → List Bool) → Prop) (allowed : W → Prop) : Prop :=
  ∀ a x tail (d : Data), allowed x → inv a d.stacks →
    d.stacks src = Encoding.frame (encode x) ++ tail →
    ∃ b, step a x b ∧ ∃ k ≤ bound, ∃ e : Data,
      inv b e.stacks ∧ e.stacks src = tail ∧ Eval body k d e

theorem rawLoop_eval (src : Fin 768) (body : Code) (encode : W → List Bool)
    (step : A → W → A → Prop) (bound : ℕ)
    (inv : A → (Fin 768 → List Bool) → Prop) (allowed : W → Prop)
    (contract : BodyContract src body encode step bound inv allowed)
    (xs : List W) (a : A) (d : Data) (hx : ∀ x ∈ xs, allowed x)
    (hi : inv a d.stacks) (hs : d.stacks src = streamBits encode xs) :
    ∃ b, FoldRel step xs a b ∧ ∃ k ≤ xs.length*(bound+2)+1, ∃ e : Data,
      inv b e.stacks ∧ e.stacks src = [] ∧
      Eval (rawLoop src body) k (afterPeek d src) e := by
  induction xs generalizing a d with
  | nil =>
    have he : d.stacks src = [] := by simpa [streamBits] using hs
    exact ⟨a,.nil a,1,by simp,afterPeek d src,hi,he,
      Eval.while_false (peek_empty d src he)⟩
  | cons x xs ih =>
    have hs' : (afterPeek d src).stacks src =
        Encoding.frame (encode x) ++ streamBits encode xs := by
      simpa [afterPeek,streamBits] using hs
    obtain ⟨b,hab,k,hk,e,hie,hse,ht⟩ := contract a x (streamBits encode xs)
      (afterPeek d src) (hx x (by simp)) hi hs'
    obtain ⟨c,hbc,m,hm,f,hif,hsf,hl⟩ := ih b e (fun y hy => hx y (by simp [hy])) hie hse
    have hne : d.stacks src ≠ [] := by
      rw [hs]
      exact rawFrames_cons_ne (encode x) (xs.map encode)
    refine ⟨c,.cons hab hbc,k+1+m+1,?_,f,hif,hsf,?_⟩
    · simp only [List.length_cons]; nlinarith
    · exact Eval.while_true (peek_nonempty d src hne) (ht.seq (peek_eval e src)) hl

theorem rawScan_eval (src : Fin 768) (body : Code) (encode : W → List Bool)
    (step : A → W → A → Prop) (bound : ℕ)
    (inv : A → (Fin 768 → List Bool) → Prop) (allowed : W → Prop)
    (contract : BodyContract src body encode step bound inv allowed)
    (xs : List W) (a : A) (d : Data) (hx : ∀ x ∈ xs, allowed x)
    (hi : inv a d.stacks) (hs : d.stacks src = streamBits encode xs) :
    ∃ b, FoldRel step xs a b ∧ ∃ k ≤ xs.length*(bound+2)+2, ∃ e : Data,
      inv b e.stacks ∧ e.stacks src = [] ∧ Eval (rawScan src body) k d e := by
  obtain ⟨b,hr,k,hk,e,hi,hs,he⟩ := rawLoop_eval src body encode step bound inv allowed contract xs a d hx hi hs
  exact ⟨b,hr,1+k,by omega,e,hi,hs,(peek_eval d src).seq he⟩
end SubexponentialSAT.SqrtLog.MomentsAssembly.Relational

end OAI.Algorithms

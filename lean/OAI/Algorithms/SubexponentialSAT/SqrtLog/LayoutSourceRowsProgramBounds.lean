import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutSourceRowsProgram

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.LayoutSourceRowsProgram
open SubexponentialSAT

theorem emittedBytes_length_le {W : Type*} (encode : W → List Bool)
    (R : ℕ → W → Prop) (L : ℕ)
    (hbound : ∀ i w, R i w → (encode w).length ≤ L)
    (ids : List ℕ) (ws : List W) (h : List.Forall₂ R ids ws) :
    (emittedBytes encode ws).length ≤ ids.length*(L+2) := by
  induction h with
  | nil => simp [emittedBytes]
  | @cons i w ids ws hr hrs ih =>
      have hw := hbound i w hr
      change ((encode w++[true,false])++emittedBytes encode ws).length ≤ _
      simp only [List.length_append,List.length_cons,List.length_nil] at *
      calc
        (encode w).length+2+(emittedBytes encode ws).length ≤ L+2+ids.length*(L+2) := by omega
        _ = (ids.length+1)*(L+2) := by ring

theorem fullSource_length_le {C : Type*} (encode : C → List Bool)
    (R : ℕ → Algorithm.Expr C → Prop) (L : ℕ)
    (hbound : ∀ i e, R i e →
      (SubexpPostfixControl.serializeCode encode e.compile).length ≤ L)
    (ids : List ℕ) (ws : List (Algorithm.Expr C)) (h : List.Forall₂ R ids ws)
    (z : C) (hz : encode z=[]) :
    (SubexpPostfixControl.serializeCode encode (foldSources (.lit z) ws).compile).length ≤
      2+ids.length*(L+2) := by
  rw [foldSources_zero_code encode z hz ws]
  have hb := emittedBytes_length_le (fun e : Algorithm.Expr C =>
    SubexpPostfixControl.serializeCode encode e.compile) R L hbound ids ws h
  simpa only [List.length_append,List.length_cons,List.length_nil] using Nat.add_le_add_left hb 2

end SubexponentialSAT.SqrtLog.LayoutSourceRowsProgram

end OAI.Algorithms

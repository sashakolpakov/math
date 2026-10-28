import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutSourceRowsProgramNative
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutSourceRowsProgramCostBase

namespace OAI.Algorithms

/-! A state-independent polynomial allowance for the complete source phase. -/
namespace SubexponentialSAT.SqrtLog.LayoutSourceRowsProgram
open SubexponentialSAT LayoutProgram
open SubexponentialSAT.SubexpLiftRing
attribute [local simp] Fin.coe_ofNat_eq_mod

def nativeRowsPolynomial {r Q d : ℕ} (p : SourceBank.Parameters r Q d) (S : ℕ) : ℕ :=
  let W := (p.R+1)*(d*baseWidth 3 p.t)
  LayoutSourceRowsProgramInitialize.budget (p.R+1) (d*baseWidth 3 p.t)+
    1000*(4*S+1)^2+
    S*(rowBudgetPolynomial (stagedSourceBudget p S)
      (Subexp.UniversalRowSourceBound.sourceLengthBound S) (p.R+1) d (baseWidth 3 p.t) S+
      45*W+83)+2*S+23

theorem nativeRowsBudget_le_polynomial {r Q d : ℕ} (p : SourceBank.Parameters r Q d)
    (s : Store) (v N f S : ℕ) (ps : List (ℕ × ℕ))
    (hv : v ≤ S) (hN : N ≤ S) (hf : f ≤ S) (hps : ps.length ≤ S)
    (hs : (LayoutOwnerFiberProgram.stream ps).length ≤ S)
    (h21 : (s 21).length ≤ S) (h26 : (s 26).length ≤ S) :
    nativeRowsBudget p s v N f S ps ≤ nativeRowsPolynomial p S := by
  have hlookup : LayoutSourcePlanLookup.pairBudget v N f ps ≤ 1000*(4*S+1)^2 :=
    (LayoutSourcePlanLookup.pairBudget_polynomial v N f ps).trans (by gcongr ; omega)
  have hidx : ps.idxOf (v,N+f) ≤ S := by
    simpa only [List.idxOf, beq_eq_decide] using
      (List.idxOf_le_length (a := (v,N+f)) (l := ps)).trans hps
  have hrow := uniformRowBudget_le_polynomial N ps (ps.length-1)
    (stagedSourceBudget p S) (Subexp.UniversalRowSourceBound.sourceLengthBound S)
    (p.R+1) d (baseWidth 3 p.t)
    ((preparedSourceStore s (p.R+1) (d*baseWidth 3 p.t) ps v N f) 21).length
    ((preparedSourceStore s (p.R+1) (d*baseWidth 3 p.t) ps v N f) 26).length S
    hN hps hs (by omega)
    (by simpa [preparedSourceStore,initializeFinish] using h21)
    (by simpa [preparedSourceStore,initializeFinish] using h26)
  dsimp only [nativeRowsBudget,nativeRowsPolynomial]
  gcongr

end SubexponentialSAT.SqrtLog.LayoutSourceRowsProgram

end OAI.Algorithms

import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.CRTLocalProgramScan
import OAI.Algorithms.SubexponentialSAT.SqrtLog.CRTLocalProgramCorrectionAlgebra
import OAI.Algorithms.SubexponentialSAT.SubexpLocalProductAlgebra

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.CRTLocalProgram
open Polynomial
open scoped BigOperators

section
variable {CodeC S R : Type*} [CommRing R]
variable (decode : CodeC → R) (denote : S → R[X]) (cm ca : CodeC → CodeC → CodeC) (pm : S → S → S)
variable (hm : ∀ a b, decode (cm a b) = decode a * decode b)
variable (ha : ∀ a b, decode (ca a b) = decode a + decode b)
variable (J : ℕ) (linear : CodeC → S)
variable (hp : ∀ a b, denote (pm a b) = Truncation.trunc J (denote a * denote b))
variable (hl : ∀ a, denote (linear a) = Truncation.trunc J (X + C (decode a)))
variable (theta minusOne : CodeC) (hn : decode minusOne = -1)
include hm ha hp hl hn

theorem localUpdate_denote (acc : S) (P : R[X])
    (hacc : denote acc = Truncation.trunc J P) (c : CodeC) :
    denote (localUpdate cm ca pm linear theta minusOne J acc c) =
      Truncation.trunc J (P * (X + C (decode theta - decode c))^J) := by
  apply truncatedPower_denote J denote pm hp _ acc _ P _ hacc J
  rw [hl, differenceValue_decode decode cm ca hm ha theta c minusOne hn]

theorem localFold_denote (cs : List CodeC) (acc : S) (P : R[X])
    (hacc : denote acc = Truncation.trunc J P) :
    denote (cs.foldl (localUpdate cm ca pm linear theta minusOne J) acc) =
      Truncation.trunc J (P * (cs.map (fun c => (X + C (decode theta - decode c))^J)).prod) := by
  induction cs generalizing acc P with
  | nil => simpa using hacc
  | cons c cs ih =>
      rw [List.foldl_cons]
      have hnext := localUpdate_denote decode denote cm ca pm hm ha J linear hp hl
        theta minusOne hn acc P hacc c
      rw [ih _ _ hnext]
      simp only [List.map_cons, List.prod_cons, mul_assoc]

theorem localScan_denote (cs : List CodeC) (skip : List Bool) (one : S)
    (hone : denote one = Truncation.trunc J 1) :
    denote (SubexpNodeScanControl.run (localUpdate cm ca pm linear theta minusOne J)
      cs ⟨one,skip,true⟩).value =
      Truncation.trunc J ((cs.eraseIdx skip.length).map
        (fun c => (X + C (decode theta - decode c))^J)).prod := by
  rw [SubexpNodeScanControl.run_skip_index]
  simpa only [one_mul] using localFold_denote decode denote cm ca pm hm ha J linear hp hl
    theta minusOne hn (cs.eraseIdx skip.length) one 1 hone

theorem localScan_localFactor {Q : ℕ} (nodes : Fin Q → CodeC) (i : Fin Q)
    (skip : List Bool) (hskip : skip.length = i.val) (one : S)
    (hone : denote one = Truncation.trunc J 1) :
    denote (SubexpNodeScanControl.run (localUpdate cm ca pm linear (nodes i) minusOne J)
      (List.ofFn nodes) ⟨one,skip,true⟩).value =
      Truncation.trunc J (TruncatedInverse.localFactor (fun j => decode (nodes j)) J i) := by
  rw [localScan_denote decode denote cm ca pm hm ha J linear hp hl
    (nodes i) minusOne hn (List.ofFn nodes) skip one hone, hskip]
  congr 1
  have h := SubexpLocalProductAlgebra.product_excluding_node (fun j => decode (nodes j)) J i
  have hof : List.ofFn (fun j => decode (nodes j)) = (List.ofFn nodes).map decode := by
    rw [List.map_ofFn]
    rfl
  rw [hof, List.eraseIdx_map, List.map_map] at h
  exact h

end
end SubexponentialSAT.SqrtLog.CRTLocalProgram

end OAI.Algorithms

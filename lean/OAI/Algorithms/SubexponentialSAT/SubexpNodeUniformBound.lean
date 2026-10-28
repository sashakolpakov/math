import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.Subexp.NodeCanonicalScale
import OAI.Algorithms.SubexponentialSAT.SubexpNodeIndexedCollector

namespace OAI.Algorithms

/-! One input-size bound and one collector cost for the entire generated
node table. The node index is still computed by the machine; its unary
length is bounded here by the number of records. -/

namespace SubexponentialSAT.SubexpNodeUniformBound

open SubexpNodeWorkspace SubexpLiftRing

def uniformSize (p D R r m : ℕ) (masters : Store)
    (nodes : List (List Bool)) (modulus zero one : List Bool)
    (scopes : List (List ℕ)) (tables : List (List Bool))
    (scalarCache : List (List (List Bool))) : ℕ :=
  Subexp.NodeCanonicalScale.originalSize p D R r (p^4-1) m masters
    (List.replicate (4*baseWidth p (D+1)) false)
    (List.replicate (4*baseWidth p (D+1)) false)
    (List.replicate (p^4-1) true) nodes modulus zero one scopes tables scalarCache

theorem thetaWord_length (p D : ℕ) [Fact p.Prime] (i : Fin (p^4-1)) :
    (SubexpNodeIndexSemantics.thetaWord p D i).length = 4*baseWidth p (D+1) := by
  unfold SubexpNodeIndexSemantics.thetaWord SubexpNodeMomentOrder.nodeWord
  simpa only [baseWidth, Nat.mul_assoc] using
    SubexpQuarticEncoding.encodeSelected_length p (D+1) (Nat.succ_pos D) _

theorem originalSize_le_uniform (p D R r m : ℕ) [Fact p.Prime]
    (masters : Store) (nodes : List (List Bool)) (modulus zero one : List Bool)
    (scopes : List (List ℕ)) (tables : List (List Bool))
    (scalarCache : List (List (List Bool))) (i : Fin (p^4-1)) :
    Subexp.NodeCanonicalScale.originalSize p D R r (p^4-1) m masters
      (SubexpNodeIndexSemantics.thetaWord p D i)
      (SubexpNodeIndexSemantics.thetaWord p D i)
      (List.replicate i.val true) nodes modulus zero one scopes tables scalarCache ≤
      uniformSize p D R r m masters nodes modulus zero one scopes tables scalarCache := by
  unfold uniformSize Subexp.NodeCanonicalScale.originalSize
  simp only [thetaWord_length, List.length_replicate]
  omega

private theorem budget_constant (bound W J : ℕ) (shape : List Bool)
    (jet : List Bool → List Bool) (records : List (List Bool))
    (hw : ∀ b ∈ records, b.length = W)
    (hj : ∀ b ∈ records, (jet b).length = J) :
    RecordPrograms.budget (SubexpNodeWideLoop.callbackCost (fun _ => bound) shape jet) records =
      records.length*(bound+16*W+3*J+2*shape.length+24) := by
  induction records with
  | nil => simp [RecordPrograms.budget]
  | cons b bs ih =>
      have hb := hw b (by simp)
      have hbj := hj b (by simp)
      have ht := ih (fun x hx => hw x (by simp [hx])) (fun x hx => hj x (by simp [hx]))
      simp only [RecordPrograms.budget, SubexpNodeWideLoop.callbackCost,
        List.length_cons, hb, hbj] at *
      rw [ht]
      ring

/-- Includes the collector's final halt, and charges both final reversals. -/
theorem collector_cost (bound W J : ℕ) (shape : List Bool)
    (jet : List Bool → List Bool) (records : List (List Bool))
    (hw : ∀ b ∈ records, b.length = W)
    (hj : ∀ b ∈ records, (jet b).length = J) :
    SubexpNodeWideLoop.totalCost (fun _ => bound) shape jet records + 1 =
      22 + records.length*(bound+33*W+6*J+2*shape.length+38) := by
  have hlength : records.map List.length = records.map (fun _ => W) :=
    List.map_congr_left hw
  have hjlength : (records.map jet).map List.length = records.map (fun _ => J) := by
    rw [List.map_map]
    exact List.map_congr_left hj
  have henc := ProgramEncoding.encodeRecords_length records
  unfold ProgramEncoding.encodeRecords at henc
  unfold SubexpNodeWideLoop.totalCost
  rw [henc, budget_constant bound W J shape jet records hw hj]
  simp only [List.length_flatten, hlength, hjlength, List.map_const',
    List.sum_replicate, smul_eq_mul]
  ring

theorem indexed_collector_cost (p D bound : ℕ) [Fact p.Prime]
    (M : SubexpPreparedQuartic.Modulus p 1) (shape : List Bool)
    (jet : Fin (p^4-1) → List Bool) (J : ℕ) (hj : ∀ i, (jet i).length = J) :
    SubexpNodeWideLoop.totalCost (fun _ => bound) shape
      (SubexpNodeIndexedCollector.indexed p D M jet)
      (SubexpNodeLiftData.liftedNodeWords p (D+1) M) + 1 =
        22+(p^4-1)*(bound+33*(4*baseWidth p (D+1))+6*J+2*shape.length+38) := by
  rw [collector_cost bound (4*baseWidth p (D+1)) J]
  · rw [SubexpNodeLiftData.liftedNodeWords_length]
  · intro b hb
    obtain ⟨i,hi⟩ := (SubexpNodeIndexSemantics.mem_liftedNodeWords_iff p (D+1) M
      (Nat.succ_pos D) b).mp hb
    rw [← hi]
    exact thetaWord_length p D i
  · intro b hb
    obtain ⟨i,hi⟩ := (SubexpNodeIndexSemantics.mem_liftedNodeWords_iff p (D+1) M
      (Nat.succ_pos D) b).mp hb
    rw [← hi]
    change (SubexpNodeIndexedCollector.indexed p D M jet
      (SubexpNodeIndexSemantics.thetaWord p D i)).length = J
    rw [SubexpNodeIndexedCollector.indexed_word]
    exact hj i

end SubexponentialSAT.SubexpNodeUniformBound

end OAI.Algorithms

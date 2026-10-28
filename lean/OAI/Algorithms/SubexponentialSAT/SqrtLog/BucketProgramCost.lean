import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.BucketProgramController
import OAI.Algorithms.SubexponentialSAT.SqrtLog.BucketProgramLabelBounds

namespace OAI.Algorithms

/-! Fully explicit bit-operation budget. Dependence on the number of
assignments is quadratic, and that number is exactly 2^h. -/
namespace SubexponentialSAT.SqrtLog.BucketProgram

theorem encoded_words_length_bound (xs : List (List Bool)) (K : ℕ)
    (hk : ∀ x∈xs,x.length ≤ K) :
    (ProgramEncoding.encodeRecords xs).length ≤ xs.length*(2*K+2)+1 := by
  induction xs with
  | nil => simp [ProgramEncoding.encodeRecords,Encoding.encodeList]
  | cons x xs ih =>
      have hx := hk x (by simp)
      have ht := ih (fun y hy => hk y (by simp [hy]))
      simp only [ProgramEncoding.encodeRecords,Encoding.encodeList,Encoding.length_frame,
        List.length_cons,List.length_append,id_eq]
      change 2*x.length+1+(ProgramEncoding.encodeRecords xs).length+1 ≤ _
      nlinarith

theorem encoded_records_length_bound (rs : List Record) (K P : ℕ)
    (hk : ∀ r∈rs,r.1.length ≤ K) (hp : ∀ r∈rs,r.2.length ≤ P) :
    (SubexponentialSAT.Subexp.BucketProgram.encodeRecords rs).length ≤ rs.length*(2*K+2*P+2) := by
  induction rs with
  | nil => simp [SubexponentialSAT.Subexp.BucketProgram.encodeRecords]
  | cons r rs ih =>
      rcases r with ⟨k,p⟩
      have hx := hk (k,p) (by simp)
      have hy := hp (k,p) (by simp)
      have ht := ih (fun q hq => hk q (by simp [hq])) (fun q hq => hp q (by simp [hq]))
      simp only [SubexponentialSAT.Subexp.BucketProgram.encodeRecords,List.length_append,
        Encoding.length_frame,List.length_cons]
      simp only at hx hy
      nlinarith

namespace Cost

def recordsBound (N K n : ℕ) : ℕ := N*(2*K+2*n+2)
def groupBound (N K n : ℕ) : ℕ :=
  9+N*(6*K+100*(recordsBound N K n+1)*(K+1)+7)+
    3*(1+(2*(2*K+1+recordsBound N K n)+2)*N)
def total (W : List Bool) (h m B n : ℕ) : ℕ :=
  let N := 2^h
  let K := Label.keyBound W h m B
  enumerationCost h+48 + (N*(Label.stepBound W h m B n+2)+1)+2 +
    120*(N*(2*K+2)+2)^2 + groupBound N K n +
    (2*recordsBound N K n+8)+1

theorem controller_cost_bound (W : List Bool) (rows : List (List (List Bool)))
    (js : List ℕ) (n h B : ℕ) (hrows : ∀ row∈rows,row.length=h)
    (hb : ∀ row∈rows,∀ x∈row,x.length ≤ B) (hlen : js.length=h) (hjs : ∀ j∈js,j < n) :
    Controller.cost W rows js n h ≤ total W h rows.length B n := by
  let rs := Controller.labelledRecords W rows js n h
  let K := Label.keyBound W h rows.length B
  have hn : rs.length=2^h := by simp [rs,Controller.labelledRecords,Label.labelled]
  have hk : ∀ r∈rs,r.1.length ≤ K := by
    intro r hr
    obtain ⟨bits,hbits,rfl⟩ := List.mem_map.mp hr
    have hbitslen := assignment_width hbits
    have hi := signatureValue_length_bound W bits rows B
      (by intro row hr; rw [hrows row hr,hbitslen]) hb
    simpa [K,Label.keyBound,Label.key,hbitslen] using hi
  have hp : ∀ r∈rs,r.2.length ≤ n := by
    intro r hr
    obtain ⟨bits,hbits,rfl⟩ := List.mem_map.mp hr
    exact (HeadScatterProgram.mask_length n js bits hjs).le
  have hraw := encoded_records_length_bound rs K n hk hp
  have hrev := encoded_records_length_bound rs.reverse K n
    (fun r hr => hk r (List.mem_reverse.mp hr))
    (fun r hr => hp r (List.mem_reverse.mp hr))
  rw [List.length_reverse,hn] at hrev
  rw [hn] at hraw
  have hkeylen : (Controller.keys rs).length ≤ 2^h := by
    have he := attainedKeys_length_le rs.reverse
    simpa [Controller.keys,hn] using he
  have hkeys : ∀ key∈Controller.keys rs,key.length ≤ K := by
    intro key hkey
    obtain ⟨p,hp⟩ := (mem_attainedKeys rs.reverse key).mp hkey
    exact hk (key,p) (List.mem_reverse.mp hp)
  have hgroup := SubexponentialSAT.Subexp.PackingBucketTable.budget_bound rs (Controller.keys rs) K hkeys
  have hgroup' : SubexponentialSAT.Subexp.PackingBucketTable.budget rs (Controller.keys rs) ≤
      groupBound (2^h) K n := by
    apply hgroup.trans
    unfold groupBound recordsBound
    gcongr
  have henc := encoded_words_length_bound (rs.map Prod.fst).reverse K (by
    intro key hkey
    obtain ⟨r,hr,rfl⟩ := List.mem_map.mp (List.mem_reverse.mp hkey)
    exact hk r hr)
  simp only [List.length_reverse,List.length_map,hn] at henc
  have hdup : Controller.dedupCost rs ≤ 120*(2^h*(2*K+2)+2)^2 := by
    unfold Controller.dedupCost
    have hbase : (ProgramEncoding.encodeRecords (rs.map Prod.fst).reverse).length+1 ≤
        2^h*(2*K+2)+2 := by
      simpa only [Nat.add_assoc, Nat.reduceAdd] using Nat.add_le_add_right henc 1
    exact Nat.mul_le_mul_left 120 (Nat.pow_le_pow_left hbase 2)
  have hlabel := Label.cost_bound W rows js n h B (assignments h) hrows hb hlen hjs
    (fun bits hbits => assignment_width hbits)
  rw [assignments_length] at hlabel
  have hclean : Controller.cleanupCost rs ≤ 2*recordsBound (2^h) K n+8 := by
    unfold Controller.cleanupCost recordsBound
    omega
  unfold Controller.cost Controller.groupCost Controller.enumerateCost total
  change enumerationCost h+48 + (Label.cost W rows js n (assignments h)+2+
      Controller.dedupCost rs+SubexponentialSAT.Subexp.PackingBucketTable.budget rs (Controller.keys rs)+
      Controller.cleanupCost rs)+1 ≤ _
  change _ ≤ enumerationCost h+48 + (2^h*(Label.stepBound W h rows.length B n+2)+1)+2+
    120*(2^h*(2*K+2)+2)^2+groupBound (2^h) K n+(2*recordsBound (2^h) K n+8)+1
  omega

end Cost
end SubexponentialSAT.SqrtLog.BucketProgram

end OAI.Algorithms

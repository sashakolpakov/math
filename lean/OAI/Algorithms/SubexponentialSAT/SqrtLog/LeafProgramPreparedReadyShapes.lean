import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgramNodeNativeDense
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgramPreparedReadyMoments

namespace OAI.Algorithms

/-! Ambient lengths of every assignment, head mask and bucket representative
are obtained from the actual produced head tables. -/
namespace SubexponentialSAT.SqrtLog.LeafProgram.PreparedReady
open SubexponentialSAT BitProgram StructuredCalls MomentsAssembly MomentsProgram
open NodeNative LeafHeadSetupProgram BucketTupleProgram
open MomentsAssembly.Relational
attribute [local simp] Fin.coe_ofNat_eq_mod

def HeadShape (n : ℕ) (h : HeadInput) : Prop :=
  h.mask.length=n ∧ ∀ x∈h.assignments,x.length=n

 theorem produced_head_shape {base : LeafHeadSetupProgram.Data} {n N D : ℕ}
    {rows : List (List Bool)} {low : List Bool}
    {Rel : ℕ → ℕ → LayoutMatrixProgram.Pair → Prop} {B z : ℕ} {table : HeadTable}
    (hp : ProducedHead base n N D rows low Rel B z table) :
    ∀ h∈table.choices,HeadShape n h := by
  obtain ⟨mr,ys,hr,hy,rfl⟩ := hp
  intro h hh
  simp only [HeadTable.choices,List.mem_reverse,List.mem_map] at hh
  obtain ⟨b,hb,rfl⟩ := hh
  exact ⟨HeadScatterProgram.mask_length _ _ _ (HeadIdentifierProgram.chosenIds_bound _ _),
    actualBuckets_width _ _ _ _ _ (HeadIdentifierProgram.chosenIds_bound _ _) b hb⟩

 theorem produced_heads_shape {base : LeafHeadSetupProgram.Data} {n N D : ℕ}
    {rows : List (List Bool)} {low : List Bool}
    {Rel : ℕ → ℕ → LayoutMatrixProgram.Pair → Prop} {B z : ℕ} {tables : List HeadTable}
    (hp : ProducedHeads base n N D rows low Rel B z tables) :
    ∀ table∈tables,∀ h∈table.choices,HeadShape n h := by
  induction hp with
  | nil => simp
  | cons hh ht ih =>
      intro table hm
      rcases List.mem_cons.mp hm with rfl|hm
      · exact produced_head_shape hh
      · exact ih table hm

 theorem enumerateFrom_property (P : HeadInput → Prop) (tables : List HeadTable)
    (rows : List (List HeadInput))
    (ht : ∀ t∈tables,∀ h∈t.choices,P h) (hr : ∀ row∈rows,∀ h∈row,P h) :
    ∀ row∈enumerateFrom tables rows,∀ h∈row,P h := by
  induction tables generalizing rows with
  | nil => exact hr
  | cons table tables ih =>
      apply ih (extend rows table.choices) (fun t hm=>ht t (by simp [hm]))
      intro row hm h hh
      simp only [extend,List.mem_reverse,List.mem_flatMap,List.mem_map] at hm
      obtain ⟨old,hold,new,hnew,rfl⟩ := hm
      rcases List.mem_append.mp hh with hh|hh
      · exact hr old hold h hh
      · have he : h=new := by simpa using hh
        subst h
        exact ht table (by simp) new hnew

 theorem preparation_bucket_shapes {s : HeadInputs} {a b : NodeNative.Data}
    (pr : Preparation s a b) :
    ∀ bucket∈pr.bucketInputs,bucket.context.length=s.n ∧
      ∀ h∈bucket.heads,HeadShape s.n h := by
  intro bucket hb
  simp only [Preparation.bucketInputs,List.mem_reverse,List.mem_map] at hb
  obtain ⟨heads,hh,rfl⟩ := hb
  have hv := enumerate_valid s.n pr.head.tables (producedHeads_valid pr.head.produced) heads hh
  have hs := enumerateFrom_property (HeadShape s.n) pr.head.tables [[]]
    (produced_heads_shape pr.head.produced) (by simp) heads hh
  exact ⟨Representative.representative_length heads _ s.n hv (by simp),hs⟩

 theorem reachable_shapes {n B d : ℕ} (vars : Finset (Fin n)) (u J : ℕ)
    (base : Fin 768 → List Bool) (ss : List (Finset (Fin n))) (bs : List BucketInput)
    (hs : ∀ bucket∈bs,bucket.context.length=n ∧ ∀ h∈bucket.heads,HeadShape n h) :
    Reachable.BucketFrames B d vars u J
      (fun high=>(high 174).length=n ∧ (high 177).length=n ∧ (high 178).length=n)
      base ss bs := by
  intro seed hseed source hsource b hb tail htail seed' hseed' source' hsource' s hsm tail' htail'
    h hh headTail hheadTail assignmentTail hat x hx
  have hbs := hs b hb
  have hhs := hbs.2 h hh
  simp only [bucketStream,bucketHigh,bucketHigh1,bucketHigh2,bucketHigh3,
    supportStream,supportHigh,headHigh,headHigh1,headHigh2,headHigh3,
    Function.update_same]
  simpa using And.intro (hhs.2 x hx) (And.intro hbs.1 hhs.1)

end SubexponentialSAT.SqrtLog.LeafProgram.PreparedReady

end OAI.Algorithms

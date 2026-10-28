import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.NodeEnvelopeWords
import OAI.Algorithms.SubexponentialSAT.SqrtLog.MomentsAssemblyProgramReachableModel

namespace OAI.Algorithms

/-! Every high tape at every reachable assignment call is bounded by the
produced bucket/support streams and the canonical sparse dictionary cap. -/
namespace SubexponentialSAT.SqrtLog.NodeEnvelope
open SubexponentialSAT MomentsAssembly MomentsProgram
open MomentsAssembly.Relational

theorem reachable_wordCap {n B d : ℕ} (vars : Finset (Fin n)) (u J A : ℕ)
    (high : Fin 768 → List Bool) (ss : List (Finset (Fin n))) (bs : List BucketInput)
    (hh : WordCap A high) (hb : (bucketsInput bs).length ≤ A)
    (hs : (rawFrames (ss.map Squarefree.encodeMask)).length ≤ A) (hn : n ≤ A)
    (he : dictionaryByteEnvelope B d (n+u+J) (dictionaryCapacity vars u J) ≤ A) :
    Reachable.BucketFrames B d vars u J (WordCap A) high ss bs := by
  intro seed hseed source hsource b hbm tail htail
  have hseed' := (dictionary_bound vars u J seed hseed).trans he
  have hbb : b.bits.length ≤ A :=
    (rawFrames_member_length_le (bs.map BucketInput.bits) b.bits
      (List.mem_map.mpr ⟨b,hbm,rfl⟩)).trans hb
  have hbctx : b.context.length ≤ A := by
    simp only [BucketInput.bits,List.length_append,Encoding.length_frame] at hbb
    omega
  have hbheads : (rawFrames (b.heads.map HeadInput.bits)).length ≤ A := by
    simp only [BucketInput.bits,List.length_append,Encoding.length_frame] at hbb
    omega
  have hbucket := bucketHigh_bound
    (bucketStream_bound hh (Product.bytes seed) source hseed' (hsource.trans hb)) b tail
    hbctx hbheads (htail.trans hb)
  intro seed' hseed' source' hsource' s hsm tail' htail'
  have hseedbytes := (dictionary_bound vars u J seed' hseed').trans he
  have hmask : (Squarefree.encodeMask s).length ≤ A := by
    simpa [Squarefree.encodeMask] using hn
  have hsupport := supportHigh_bound
    (supportStream_bound hbucket (Product.bytes seed') source' hseedbytes (hsource'.trans hs))
    (Squarefree.encodeMask s) tail' hmask (htail'.trans hs)
  intro h hhm headTail hheadTail
  have hhbits : h.bits.length ≤ A :=
    (rawFrames_member_length_le (b.heads.map HeadInput.bits) h.bits
      (List.mem_map.mpr ⟨h,hhm,rfl⟩)).trans hbheads
  have hhmasks : h.mask.length ≤ A ∧ h.context.length ≤ A ∧
      (rawFrames h.assignments).length ≤ A := by
    simp only [HeadInput.bits,List.length_append,Encoding.length_frame] at hhbits
    omega
  have hhead := headHigh_bound hsupport h headTail hhmasks.1 hhmasks.2.1 hhmasks.2.2
    (hheadTail.trans hbheads)
  intro assignmentTail hat x hxm
  have hx := (rawFrames_member_length_le h.assignments x hxm).trans hhmasks.2.2
  exact (hhead.update _ _ (hat.trans hhmasks.2.2)).update _ _ hx

theorem reachable_mono {n B d : ℕ} (vars : Finset (Fin n)) (u J : ℕ)
    (P Q : (Fin 768 → List Bool) → Prop) (high : Fin 768 → List Bool)
    (ss : List (Finset (Fin n))) (bs : List BucketInput)
    (hp : Reachable.BucketFrames B d vars u J P high ss bs)
    (hPQ : ∀ high,P high → Q high) :
    Reachable.BucketFrames B d vars u J Q high ss bs := by
  intro seed hseed source hsource b hb tail htail seed' hseed' source' hsource' s hs tail' htail'
    h hh headTail hheadTail assignmentTail hat x hx
  exact hPQ _ (hp seed hseed source hsource b hb tail htail seed' hseed'
    source' hsource' s hs tail' htail' h hh headTail hheadTail assignmentTail hat x hx)

end SubexponentialSAT.SqrtLog.NodeEnvelope

end OAI.Algorithms

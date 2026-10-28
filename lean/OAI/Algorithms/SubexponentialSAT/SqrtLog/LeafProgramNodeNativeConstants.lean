import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgramNodeNativeCore

namespace OAI.Algorithms

/-! The physical sparse-one cache is exactly the encoded origin entry. -/
noncomputable section
namespace SubexponentialSAT.SqrtLog.LeafProgram.NodeNative
open SubexponentialSAT BitProgram StructuredCalls LeafHeadSetupProgram
open SubexponentialSAT.SubexpLiftRing SubexponentialSAT.SubexpQuarticRing MomentsProgram MomentsAssembly
attribute [local simp] Fin.coe_ofNat_eq_mod

def originEntries {n B d : ℕ} (one : RingProgram.Code (Word B) d) : List (Product.Entry n B d) :=
  [(Squarefree.Index.origin,one)]

theorem originEntries_valid {n B d : ℕ} (one : RingProgram.Code (Word B) d)
    (vars : Finset (Fin n)) (u J : ℕ) (hu : 0 < u) (hJ : 0 < J) :
    EntryInvariant vars u J (originEntries one) := by
  constructor
  · intro e he
    simp only [originEntries,List.mem_singleton] at he
    subst e
    simp [Product.ValidKey,Squarefree.Index.origin,Squarefree.Index.Kept,Squarefree.Index.Valid,hu,hJ]
  · simp [originEntries,Squarefree.Sparse.keys]

theorem Preparation.one_entries {s : HeadInputs} {a b : Data} (pr : Preparation s a b)
    (ha : Ready s a) {B d : ℕ} (one : RingProgram.Code (Word B) d)
    (h207 : a.stacks 207=RingProgram.flat one) :
    b.stacks 69=Product.bytes (originEntries (n:=s.n) one) ∧
      b.stacks 167=Product.bytes (originEntries (n:=s.n) one) := by
  have h128 : (loadedState a).stacks 128=unary s.n := ha.heads.ambient
  have h207' : (loadedState a).stacks 207=RingProgram.flat one :=
    (LayoutMasters.loaded_frame (LayoutMasters.project a) 207 (not_low_of_ge (by decide))).trans h207
  have he : LeafNodeCacheProgram.rawOne (loadedState a).stacks =
      Product.bytes (originEntries (n:=s.n) one) := by
    simp [LeafNodeCacheProgram.rawOne,h128,h207',unary,HashCircuitProgram.Constant.key_eq_origin,
      originEntries,Product.bytes,Normalize.bytes,Squarefree.Program.rawEntries,
      Squarefree.Program.encodeDictionary]
  exact ⟨(pr.one_word ha).1.trans he,(pr.one_word ha).2.trans he⟩

theorem Preparation.shape_word {s : HeadInputs} {a b : Data} (pr : Preparation s a b)
    (ha : Ready s a) : b.stacks 191=unary s.n :=
  (pr.direct_word ha (128,191) (by decide)).trans ha.heads.ambient

theorem Preparation.zero_word {s : HeadInputs} {a b : Data} (pr : Preparation s a b)
    (ha : Ready s a) {B d : ℕ} (zero : RingProgram.Code (Word B) d)
    (h280 : a.stacks 280=RingProgram.flat zero) : b.stacks 190=RingProgram.flat zero :=
  (pr.direct_master ha (280,190) (by decide) (by decide)).trans h280

theorem Preparation.output_empty {s : HeadInputs} {a b : Data} (pr : Preparation s a b)
    (h102 : a.stacks 102=[]) : b.stacks 102=[] :=
  (pr.frame 102 (by rw [Node.mem_cleanup]; norm_num)).trans h102

theorem Preparation.support_cap {s : HeadInputs} {a b : Data} (pr : Preparation s a b)
    (J : ℕ) (h243 : a.stacks 243=List.replicate J true) :
    (∀ S,S∈pr.supports ↔ S.card < J) ∧ pr.supports.length=SupportProgram.count s.n J := by
  simpa [h243] using And.intro pr.supports_all pr.supports_count

end SubexponentialSAT.SqrtLog.LeafProgram.NodeNative

end

end OAI.Algorithms

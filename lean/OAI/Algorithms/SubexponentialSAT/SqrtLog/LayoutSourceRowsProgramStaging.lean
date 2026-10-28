import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutSourceRowsProgramSourceFrame

namespace OAI.Algorithms

/-! The source numerator uses empty scalar work tapes5/10. The polynomial
executor retains its modulus/width there. Two reversible transfers isolate
these phases without touching the native high arithmetic cache. -/
namespace SubexponentialSAT.SqrtLog.LayoutSourceRowsProgram
open SubexponentialSAT BitProgram StructuredCalls
attribute [local simp] Fin.coe_ofNat_eq_mod

def clearedSourceStore (s : Store) : Store := Function.update (Function.update s 5 []) 10 []
def stagedSourceStore (s : Store) : Store :=
  Function.update (Function.update (clearedSourceStore s) 335 (s 5).reverse) 336 (s 10).reverse

def stageScalarWork : Code := .seq (transfer 5 335) (transfer 10 336)
def unstageScalarWork : Code := .seq (transfer 335 5) (transfer 336 10)
def stagedPackedSource : Code := .seq stageScalarWork (.seq packedSource unstageScalarWork)

theorem stageScalarWork_run (s : Store) (h335 : s 335=[]) (h336 : s 336=[]) :
    ExecutesIn stageScalarWork (3*(s 5).length+3*(s 10).length+6) s (stagedSourceStore s) := by
  let s1 := Function.update (Function.update s 5 []) 335 (s 5).reverse
  have h1 : ExecutesIn (transfer 5 335) (3*(s 5).length+3) s s1 := by
    simpa [s1,h335] using transfer_run 5 335 s (by decide)
  have h2 := transfer_run 10 336 s1 (by decide)
  have he : Function.update (Function.update s1 10 []) 336 ((s1 10).reverse++s1 336)=stagedSourceStore s := by
    funext i
    simp only [s1,stagedSourceStore,clearedSourceStore,Function.update_apply]
    split_ifs <;> simp_all
  rw [he] at h2
  convert h1.seq h2 using 1 <;> simp [stageScalarWork,s1] ; omega

theorem unstageScalarWork_run (s : Store) (bits : List Bool)
    (h335 : s 335=[]) (h336 : s 336=[]) :
    ExecutesIn unstageScalarWork (3*(s 5).length+3*(s 10).length+6)
      (Function.update (stagedSourceStore s) 287 bits) (Function.update s 287 bits) := by
  let a := Function.update (stagedSourceStore s) 287 bits
  let b := Function.update (Function.update a 335 []) 5 ((a 335).reverse++a 5)
  have h1 := transfer_run 335 5 a (by decide)
  have h2 := transfer_run 336 10 b (by decide)
  have he : Function.update (Function.update b 336 []) 10 ((b 336).reverse++b 10)=
      Function.update s 287 bits := by
    funext i
    by_cases hi335 : i=335
    · subst i; simp [b,a,stagedSourceStore,clearedSourceStore,h335]
    by_cases hi336 : i=336
    · subst i; simp [b,a,stagedSourceStore,clearedSourceStore,h336]
    by_cases hi5 : i=5
    · subst i; simp [b,a,stagedSourceStore,clearedSourceStore]
    by_cases hi10 : i=10
    · subst i; simp [b,a,stagedSourceStore,clearedSourceStore]
    by_cases hi287 : i=287
    · subst i; simp [b,a,stagedSourceStore,clearedSourceStore]
    simp [b,a,stagedSourceStore,clearedSourceStore,
      hi335,hi336,hi5,hi10,hi287]
  rw [he] at h2
  convert h1.seq h2 using 1 <;> simp [unstageScalarWork,b,a,stagedSourceStore,clearedSourceStore] ; omega

theorem stagedSourceStore_projection (s : Store) :
    stagedSourceStore s ∘ sourcePorts=clearedSourceStore s ∘ sourcePorts := by
  funext i
  have hi : (sourcePorts i).val < 320 := i.isLt
  have h335 : sourcePorts i≠335 := by intro h; rw [h] at hi; norm_num at hi
  have h336 : sourcePorts i≠336 := by intro h; rw [h] at hi; norm_num at hi
  simp [stagedSourceStore,h335,h336]

theorem stagedSourceStore_fiber (s : Store) (ids : List ℕ) (acc : List Bool) (i : ℕ) :
    stagedSourceStore (Function.update (fiberState s ids acc) 305 (List.replicate i true))=
      Function.update (fiberState (stagedSourceStore s) ids acc) 305 (List.replicate i true) := by
  funext j
  simp only [stagedSourceStore,clearedSourceStore,fiberState,Function.update_apply]
  split_ifs <;> simp_all

theorem stagedPackedSource_eval {W : Type*} (encode : W → List Bool) (R : W → Prop)
    (K : ℕ) (s : Store) (h335 : s 335=[]) (h336 : s 336=[])
    (hraw : ∀ regs,∃ w n rf,R w ∧ n ≤ K ∧ Eval packedSource n
      (⟨regs,stagedSourceStore s⟩ : Data)
      (⟨rf,Function.update (stagedSourceStore s) 287 (encode w)⟩ : Data))
    (regs : Fin 16 → Bool) :
    ∃ w n rf,R w ∧ n ≤ K+6*(s 5).length+6*(s 10).length+12 ∧
      Eval stagedPackedSource n (⟨regs,s⟩ : Data)
        (⟨rf,Function.update s 287 (encode w)⟩ : Data) := by
  obtain ⟨n1,r1,hn1,he1⟩ := stageScalarWork_run s h335 h336 regs
  obtain ⟨w,n2,r2,hw,hn2,he2⟩ := hraw r1
  obtain ⟨n3,r3,hn3,he3⟩ := unstageScalarWork_run s (encode w) h335 h336 r2
  exact ⟨w,n1+(n2+n3),r3,hw,by omega,he1.seq (he2.seq he3)⟩

end SubexponentialSAT.SqrtLog.LayoutSourceRowsProgram

end OAI.Algorithms

import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutSourceRowsProgramStagedPacked
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutSourceRowsProgramModelAssembly
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutSourceRowsProgramAbsent
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutSourceRowsProgramConcrete

namespace OAI.Algorithms

/-! Complete source-table execution from physical layout metadata and ring
caches. No polynomial table or source-command service is an input. -/
namespace SubexponentialSAT.SqrtLog.LayoutSourceRowsProgram
open SubexponentialSAT BitProgram StructuredCalls SubexponentialSAT.Subexp
open SubexponentialSAT.Subexp.ConstructivePacking SubexponentialSAT.MulticolorTypes LayoutProgram
open SubexponentialSAT.SubexpLiftRing

def nativeRowsBudget {r Q d : ℕ} (p : SourceBank.Parameters r Q d)
    (s : Store) (v N f S : ℕ) (ps : List (ℕ × ℕ)) : ℕ :=
  let W := (p.R+1)*(d*baseWidth 3 p.t)
  let K := uniformRowBudget N ps (ps.length-1) (stagedSourceBudget p S)
    (Subexp.UniversalRowSourceBound.sourceLengthBound S) (p.R+1) d (baseWidth 3 p.t)
    ((preparedSourceStore s (p.R+1) (d*baseWidth 3 p.t) ps v N f) 21).length
    ((preparedSourceStore s (p.R+1) (d*baseWidth 3 p.t) ps v N f) 26).length
  LayoutSourceRowsProgramInitialize.budget (p.R+1) (d*baseWidth 3 p.t)+
    LayoutSourcePlanLookup.pairBudget v N f ps+N*(K+45*W+83)+
    2*(ps.idxOf (v,N+f))+23

theorem sourceRows_run {r Q d : ℕ} (p : SourceBank.Parameters r Q d)
    (ps : List (ℕ × ℕ)) (P : PackingData (Fin ps.length) (UniversalType r Q 1))
    (s : Store) (v N f S : ℕ) (width : List Bool) (frame : Fin 6 → List Bool)
    (hinit : LayoutSourceRowsProgramInitialize.Ready (s ∘ initializationPorts)
      (p.R+1) (d*baseWidth 3 p.t))
    (hv : s 233=LayoutSourcePlanLookup.unary v)
    (hN : s 212=LayoutSourcePlanLookup.unary N)
    (hf : s 216=LayoutSourcePlanLookup.unary f)
    (hplan : s 337=LayoutOwnerFiberProgram.stream ps)
    (hlookup : LayoutSourcePlanLookup.Native.Clean
      (⟨fun _ => false,initializeFinish s (p.R+1) (d*baseWidth 3 p.t)⟩ : Data))
    (hclean : RowsClean (preparedSourceStore s (p.R+1) (d*baseWidth 3 p.t) ps v N f))
    (hwork : RowWorkClean (preparedSourceStore s (p.R+1) (d*baseWidth 3 p.t) ps v N f))
    (howner : ∀ i : Fin 11, (2 : ℕ) ≤ i.val →
      (preparedSourceStore s (p.R+1) (d*baseWidth 3 p.t) ps v N f) (ownerStacks i)=[])
    (H : DensePolynomialProgram.PairSpec.BaseReady 3 p.t p.modulus p.cache
      (HornerProgram.modelTable p.t p.model p.modulus p.cache) (s ∘ executorPorts) width frame)
    (E : LayoutSourceRowsProgramReadiness.Empty s)
    (hready : SourceBank.Ready p (⟨fun _ => false,
      clearedSourceStore (preparedSourceStore s (p.R+1) (d*baseWidth 3 p.t) ps v N f) ∘ sourcePorts⟩ : SourceBank.Data))
    (hsourceClean : ∀ j∈SourceBank.cleanupPorts,
      (preparedSourceStore s (p.R+1) (d*baseWidth 3 p.t) ps v N f) (sourcePorts j)=[])
    (hmeta : s 306=SelectorProgram.rawRecords (SourceBank.metadataRecords P))
    (hsize : ∀ j : Fin 320,
      ((preparedSourceStore s (p.R+1) (d*baseWidth 3 p.t) ps v N f) (sourcePorts j)).length ≤ S)
    (hmetadata : ∀ x,SourceBank.MetadataBound (PackingMetadata.value P CollisionProgram.encodeType x) S)
    (hD : ps.length ≤ S) (hQ : Q ≤ S) (hR : p.R ≤ S)
    (hW : p.ringWidth.length ≤ S) (hRW : p.rowWidth.length ≤ S)
    (regs : Fin 16 → Bool) :
    ∃ rows n rf,
      RowProperty DensePolynomialProgram.encode
        (fun j out => PolynomialExecutorProgram.meaning p.ops out=
          sourceRowFamily ps N f v (totalPackedSource p P) j)
        ((p.R+1)*(d*baseWidth 3 p.t)) 0 rows ∧ rows.length=N ∧
      n ≤ nativeRowsBudget p s v N f S ps ∧
      Eval sourceRows n (⟨regs,s⟩ : Data)
        (⟨rf,Function.update (initializeFinish s (p.R+1) (d*baseWidth 3 p.t)) 205
          (Encoding.encodeList DensePolynomialProgram.encode rows)⟩ : Data) := by
  by_cases hmem : (v,N+f)∈ps
  · have hidx := (LayoutSourcePlanLookup.pair_index_mem ps (v,N+f) hmem).1
    let row : Fin ps.length := ⟨ps.idxOf (v,N+f),hidx⟩
    let base := preparedSourceStore s (p.R+1) (d*baseWidth 3 p.t) ps v N f
    have hs := fun j (hj : j < N) remaining acc =>
      staged_native_row_relSourceSpec p P row base (ps.length-1) S (by omega) (by omega)
        (hwork 335 (by simp)) (hwork 336 (by simp)) hready hsourceClean
        (by simpa [base,preparedSourceStore,initializeFinish] using hmeta)
        (by simp [base,preparedSourceStore,row,LayoutSourcePlanLookup.unary])
        hsize hmetadata hQ hR hW hRW j remaining acc
    obtain ⟨rows,n,rf,hrows,hlen,hn,he⟩ := sourceRows_present_model
      p.t p.ht p.hd p.model p.modulus p.cache p.hz p.R width frame
      stagedPackedSource s v N f (stagedSourceBudget p S)
      (Subexp.UniversalRowSourceBound.sourceLengthBound S) ps (packedSourceValue p P row)
      hinit hv hN hf hplan hmem hlookup hclean hwork howner H E hs
      (fun i _ => packedSourceValue_degree p P row i) regs
    have hvalue : totalPackedSource p P (ps.idxOf (v,N+f))=packedSourceValue p P row := by
      funext col
      simp [totalPackedSource,hidx,row]
    have hrel : (fun j out => PolynomialExecutorProgram.meaning p.ops out=
        ownerSum ps j (packedSourceValue p P row))=
        (fun j out => PolynomialExecutorProgram.meaning p.ops out=
          sourceRowFamily ps N f v (totalPackedSource p P) j) := by
      funext j out
      simp only [sourceRowFamily,ite_eq_left hmem,hvalue]
    refine ⟨rows,n,rf,?_,hlen,?_,he⟩
    · change RowProperty DensePolynomialProgram.encode _ _ _ _ at hrows
      rw [←hrel]
      exact hrows
    · apply hn.trans
      dsimp only [nativeRowsBudget]
      gcongr <;> omega
  · obtain ⟨rows,n,rf,hrows,hlen,hn,he⟩ := sourceRows_absent_model
      p.t p.ht p.hd p.model p.modulus p.cache p.hz stagedPackedSource s (p.R+1) v N f ps
      hinit hv hN hf hplan hmem hlookup hclean regs
    have hrel : (fun (_ : ℕ) out => PolynomialExecutorProgram.meaning p.ops out=0)=
        (fun j out => PolynomialExecutorProgram.meaning p.ops out=
          sourceRowFamily ps N f v (totalPackedSource p P) j) := by
      funext j out
      simp [sourceRowFamily,hmem]
    refine ⟨rows,n,rf,?_,hlen,?_,he⟩
    · rw [←hrel]
      exact hrows
    · apply hn.trans
      dsimp only [nativeRowsBudget]
      gcongr <;> omega

end SubexponentialSAT.SqrtLog.LayoutSourceRowsProgram

end OAI.Algorithms

import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutSourceRowsProgramAssembly
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutSourceRowsProgramOutput

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.LayoutSourceRowsProgram
open SubexponentialSAT BitProgram StructuredCalls
open SubexponentialSAT.SubexpLiftRing SubexponentialSAT.SubexpQuarticRing

theorem sourceRows_absent_model (t : ℕ) (ht : 0 < t) {d : ℕ} (hd : 0 < d)
    (a : RingModel.Data d) (M : SubexpPreparedQuartic.Modulus 3 t)
    (cache : RingProgram.ScalarCache 3 t) (hz : BinaryArithmetic.toNat cache.zero.val < 3^t)
    (source : Code) (s : Store) (D v N f : ℕ) (ps : List (ℕ × ℕ))
    (hinit : LayoutSourceRowsProgramInitialize.Ready (s ∘ initializationPorts) D (d*baseWidth 3 t))
    (hv : s 233=LayoutSourcePlanLookup.unary v)
    (hN : s 212=LayoutSourcePlanLookup.unary N)
    (hf : s 216=LayoutSourcePlanLookup.unary f)
    (hplan : s 337=LayoutOwnerFiberProgram.stream ps)
    (hmem : (v,N+f) ∉ ps)
    (hlookup : LayoutSourcePlanLookup.Native.Clean
      (⟨fun _ => false,initializeFinish s D (d*baseWidth 3 t)⟩ : Data))
    (hclean : RowsClean (preparedSourceStore s D (d*baseWidth 3 t) ps v N f))
    (regs : Fin 16 → Bool) :
    ∃ rows n rf,
      RowProperty DensePolynomialProgram.encode
        (fun _ out => PolynomialExecutorProgram.meaning (RingProgram.modelRing t ht hd a M cache) out=0)
        (D*(d*baseWidth 3 t)) 0 rows ∧ rows.length=N ∧
      n ≤ LayoutSourceRowsProgramInitialize.budget D (d*baseWidth 3 t)+
        LayoutSourcePlanLookup.pairBudget v N f ps+N*(26*(D*(d*baseWidth 3 t))+44)+
        2*(ps.idxOf (v,N+f))+23 ∧
      Eval (sourceRowsWith source) n (⟨regs,s⟩ : Data)
        (⟨rf,Function.update (initializeFinish s D (d*baseWidth 3 t)) 205
          (Encoding.encodeList DensePolynomialProgram.encode rows)⟩ : Data) := by
  let z := (RingProgram.modelProgram t a M cache).zeroRun.1
  let zs := List.replicate D z
  let rows := List.replicate N zs
  have hb : DensePolynomialProgram.encode zs=List.replicate (D*(d*baseWidth 3 t)) false :=
    LayoutSourceRowsProgramInitialize.encode_zero_array z
      (DensePolynomialProgram.model_zero_bits t a M cache hz) D
  have hzvalue : (RingProgram.modelRing t ht hd a M cache).decode z=0 :=
    (RingProgram.modelRing t ht hd a M cache).zero_correct
  have hm : PolynomialExecutorProgram.meaning (RingProgram.modelRing t ht hd a M cache) zs=0 := by
    dsimp only [zs]
    induction D with
    | zero => simp [PolynomialExecutorProgram.meaning]
    | succ D ih =>
        simp only [PolynomialExecutorProgram.meaning] at ih ⊢
        simp [List.replicate_succ,hzvalue]
  have hp : RowProperty DensePolynomialProgram.encode
      (fun _ out => PolynomialExecutorProgram.meaning (RingProgram.modelRing t ht hd a M cache) out=0)
      (D*(d*baseWidth 3 t)) 0 rows :=
    RowProperty.replicate _ _ _ zs (fun _ => hm) (by simp [hb]) 0 N
  obtain ⟨n,rf,hn,he⟩ := sourceRows_absent source s D (d*baseWidth 3 t) v N f ps
    hinit hv hN hf hplan hmem hlookup hclean regs
  refine ⟨rows,n,rf,hp,by simp [rows],hn,?_⟩
  have heq : Encoding.encodeList id (List.replicate N (List.replicate (D*(d*baseWidth 3 t)) false))=
      Encoding.encodeList DensePolynomialProgram.encode rows := by
    rw [←hb]
    exact encodeList_replicate _ zs N
  simpa only [heq] using he

end SubexponentialSAT.SqrtLog.LayoutSourceRowsProgram

end OAI.Algorithms

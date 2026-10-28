import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutSourceRowsProgramRow

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.LayoutSourceRowsProgram
open SubexponentialSAT BitProgram StructuredCalls
open SubexponentialSAT.SubexpLiftRing SubexponentialSAT.SubexpQuarticRing
attribute [local simp] Fin.coe_ofNat_eq_mod

def RowWorkClean (s : Store) : Prop :=
  ∀ i∈([27,28,29,287,305,333,335,336] : List (Fin 340)), s i=[]

theorem sourceRows_relSpec (t : ℕ) (ht : 0 < t) {d : ℕ} (hd : 0 < d)
    (a : RingModel.Data d) (M : SubexpPreparedQuartic.Modulus 3 t)
    (cache : RingProgram.ScalarCache 3 t) (hz : BinaryArithmetic.toNat cache.zero.val < 3^t)
    (D : ℕ) (width : List Bool) (frame : Fin 6 → List Bool)
    (source : Code) (base : Store) (I K L N : ℕ) (ps : List (ℕ × ℕ))
    (value : ℕ → ℕ → Polynomial (a.O t))
    (spec : ∀ j, j < N → ∀ remaining acc,
      RelSourceSpec source (rowState base j remaining acc)
        (fun e : Algorithm.Expr (List (PolynomialExecutorProgram.Coeff (baseWidth 3 t) d)) =>
          SubexpPostfixControl.serializeCode DensePolynomialProgram.encode e.compile)
        (TypedSourceRel DensePolynomialProgram.encode
          (PolynomialExecutorProgram.meaning (RingProgram.modelRing t ht hd a M cache)) (value j) L) I K L)
    (hs : base 337=LayoutOwnerFiberProgram.stream ps)
    (howner : ∀ i : Fin 11, 2 ≤ i.val → base (ownerStacks i)=[])
    (hwork : RowWorkClean base)
    (hI : ∀ j, j < N → ∀ i∈LayoutOwnerFiberProgram.fiberIndices j 0 ps, i ≤ I)
    (H : PolynomialExecutorProgram.Ready 3 t M cache (RingProgram.modelProgram t a M cache)
      (HornerProgram.modelTable t a M cache) D width frame
        (executionContext (evaluationInput base))) :
    RelRowSpec (sourceRowWith source) base DensePolynomialProgram.encode
      (fun j out => PolynomialExecutorProgram.meaning (RingProgram.modelRing t ht hd a M cache) out=
        Truncation.trunc D (ownerSum ps j (value j))) N
      (uniformRowBudget N ps I K L D d (baseWidth 3 t) (base 21).length (base 26).length)
      (D*(d*baseWidth 3 t)) := by
  intro j hj remaining acc regs
  let s := rowState base j remaining acc
  have howner' : ∀ i : Fin 11, 2 ≤ i.val → s (ownerStacks i)=[] := by
    intro i hi
    have hh := howner i hi
    fin_cases i <;> simp_all [s,rowState,ownerStacks]
  have H' : PolynomialExecutorProgram.Ready 3 t M cache (RingProgram.modelProgram t a M cache)
      (HornerProgram.modelTable t a M cache) D width frame
        (executionContext (evaluationInput s)) := by
    simpa only [s,executionContext_evaluation_rowState] using H
  obtain ⟨out,n,rf,hlen,hmeaning,hn,he⟩ := sourceRowWith_run t ht hd a M cache hz D width frame
    source s I K L (value j) (spec j hj remaining acc) j ps
    (by simp [s,rowState,LayoutOwnerFiberProgram.unary])
    (by simpa [s,rowState] using hs) howner'
    (by simpa [s,rowState] using hwork 305 (by simp))
    (by simpa [s,rowState] using hwork 287 (by simp))
    (by simpa [s,rowState] using hwork 333 (by simp)) (hI j hj)
    (by simpa [s,rowState] using hwork 27 (by simp))
    (by simpa [s,rowState] using hwork 28 (by simp))
    (by simpa [s,rowState] using hwork 29 (by simp))
    (by simpa [s,rowState] using hwork 335 (by simp))
    (by simpa [s,rowState] using hwork 336 (by simp)) H' regs
  refine ⟨out,n,rf,hmeaning,?_,?_,he⟩
  · simp [DensePolynomialProgram.encode_length,hlen]
  · have hb := sourceRowBudget_le_uniform j N (by omega) ps I K L D d (baseWidth 3 t)
      (base 21).length (base 26).length
    apply le_trans _ hb
    simpa [s,rowState] using hn

end SubexponentialSAT.SqrtLog.LayoutSourceRowsProgram

end OAI.Algorithms

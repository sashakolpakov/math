import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutSourceRowsProgramTyped
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutSourceRowsProgramModel
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutOwnerFiberProgramBounds

namespace OAI.Algorithms

/-! One source row: actual owner scan, native per-incidence source generation,
postfix summation, and native polynomial evaluation. -/
namespace SubexponentialSAT.SqrtLog.LayoutSourceRowsProgram
open SubexponentialSAT BitProgram StructuredCalls
open SubexponentialSAT.SubexpLiftRing SubexponentialSAT.SubexpQuarticRing

def sourceRowWith (source : Code) : Code :=
  .seq (sourceForOwner source) (evaluateRow PolynomialExecutorProgram.flatProgram)

def sourceRowBudget (query : ℕ) (ps : List (ℕ × ℕ)) (I K L D d B a b : ℕ) : ℕ :=
  let F := (LayoutOwnerFiberProgram.fiberIndices query 0 ps).length
  let S := 2+F*(L+2)
  LayoutOwnerFiberProgram.budget query ps+F*(K+5*I+3*L+15)+
    300000*(S+1)*(D+1)^3*(d+1)^3*(B+1)^2+18*(D*(d*B))+
    6*a+6*b+3*S+67

def uniformRowBudget (N : ℕ) (ps : List (ℕ × ℕ)) (I K L D d B a b : ℕ) : ℕ :=
  let S := 2+ps.length*(L+2)
  1000*((LayoutOwnerFiberProgram.stream ps).length+N+1)^2+
    ps.length*(K+5*I+3*L+15)+
    300000*(S+1)*(D+1)^3*(d+1)^3*(B+1)^2+18*(D*(d*B))+
    6*a+6*b+3*S+67

theorem sourceRowBudget_le_uniform (query N : ℕ) (hq : query ≤ N)
    (ps : List (ℕ × ℕ)) (I K L D d B a b : ℕ) :
    sourceRowBudget query ps I K L D d B a b ≤ uniformRowBudget N ps I K L D d B a b := by
  have hF := LayoutOwnerFiberProgram.fiberIndices_length_le query 0 ps
  have howner : LayoutOwnerFiberProgram.budget query ps ≤
      1000*((LayoutOwnerFiberProgram.stream ps).length+N+1)^2 :=
    (LayoutOwnerFiberProgram.budget_polynomial query ps).trans (by gcongr)
  dsimp only [sourceRowBudget,uniformRowBudget]
  gcongr

theorem sourceRowWith_run (t : ℕ) (ht : 0 < t) {d : ℕ} (hd : 0 < d)
    (a : RingModel.Data d) (M : SubexpPreparedQuartic.Modulus 3 t)
    (cache : RingProgram.ScalarCache 3 t) (hz : BinaryArithmetic.toNat cache.zero.val < 3^t)
    (D : ℕ) (width : List Bool) (frame : Fin 6 → List Bool)
    (source : Code) (base : Store) (I K L : ℕ)
    (value : ℕ → Polynomial (a.O t))
    (spec : RelSourceSpec source base
      (fun e : Algorithm.Expr (List (PolynomialExecutorProgram.Coeff (baseWidth 3 t) d)) =>
        SubexpPostfixControl.serializeCode DensePolynomialProgram.encode e.compile)
      (TypedSourceRel DensePolynomialProgram.encode
        (PolynomialExecutorProgram.meaning (RingProgram.modelRing t ht hd a M cache)) value L) I K L)
    (query : ℕ) (ps : List (ℕ × ℕ))
    (hq : base 320=LayoutOwnerFiberProgram.unary query)
    (hs : base 337=LayoutOwnerFiberProgram.stream ps)
    (hclean : ∀ i : Fin 11, 2 ≤ i.val → base (ownerStacks i)=[])
    (h305 : base 305=[]) (h287 : base 287=[]) (h333 : base 333=[])
    (hI : ∀ i∈LayoutOwnerFiberProgram.fiberIndices query 0 ps, i ≤ I)
    (h27 : base 27=[]) (h28 : base 28=[]) (h29 : base 29=[])
    (h335 : base 335=[]) (h336 : base 336=[])
    (H : PolynomialExecutorProgram.Ready 3 t M cache (RingProgram.modelProgram t a M cache)
      (HornerProgram.modelTable t a M cache) D width frame
        (executionContext (evaluationInput base)))
    (regs : Fin 16 → Bool) :
    ∃ out : List (PolynomialExecutorProgram.Coeff (baseWidth 3 t) d), ∃ n rf,
      out.length=D ∧
      PolynomialExecutorProgram.meaning (RingProgram.modelRing t ht hd a M cache) out=
        Truncation.trunc D (ownerSum ps query value) ∧
      n ≤ sourceRowBudget query ps I K L D d (baseWidth 3 t) (base 21).length (base 26).length ∧
      Eval (sourceRowWith source) n (⟨regs,base⟩ : Data)
        (⟨rf,Function.update base 240 (DensePolynomialProgram.encode out)⟩ : Data) := by
  let decode := PolynomialExecutorProgram.meaning (RingProgram.modelRing t ht hd a M cache)
  obtain ⟨e,n1,r1,hevalue,helen,hn1,he1⟩ := sourceForOwner_typed
    DensePolynomialProgram.encode decode value [] rfl
    (by simp [decode,PolynomialExecutorProgram.meaning])
    source base I K L spec query ps hq hs hclean h305 h287 h333 hI regs
  let bits := SubexpPostfixControl.serializeCode DensePolynomialProgram.encode e.compile
  let s1 := Function.update base 333 bits.reverse
  have H1 : PolynomialExecutorProgram.Ready 3 t M cache (RingProgram.modelProgram t a M cache)
      (HornerProgram.modelTable t a M cache) D width frame
        (executionContext (evaluationInput s1)) := by
    simpa only [s1,executionContext_evaluation_update333] using H
  obtain ⟨out,hlen,hmeaning,hr⟩ := evaluateModel_run t ht hd a M cache hz D width frame s1 H1 e
    (by simp [s1,bits]) (by simp [s1,h27]) (by simp [s1,h28]) (by simp [s1,h29])
    (by simp [s1,h335]) (by simp [s1,h336])
  obtain ⟨n2,r2,hn2,he2⟩ := hr r1
  have hfinish : Function.update (Function.update s1 333 []) 240
      (DensePolynomialProgram.encode out)=Function.update base 240 (DensePolynomialProgram.encode out) := by
    funext i
    by_cases hi : i=333 <;>
      simp [s1,Function.update_apply,hi,h333]
  rw [hfinish] at he2
  refine ⟨out,n1+n2,r2,hlen,?_,?_,he1.seq he2⟩
  · dsimp only [decode] at hevalue
    simpa only [hevalue] using hmeaning
  · have hlen1 : (s1 333).length ≤
        2+(LayoutOwnerFiberProgram.fiberIndices query 0 ps).length*(L+2) := by
      simpa [s1,bits] using helen
    have hpoly : 300000*((s1 333).length+1)*(D+1)^3*(d+1)^3*(baseWidth 3 t+1)^2 ≤
        300000*(2+(LayoutOwnerFiberProgram.fiberIndices query 0 ps).length*(L+2)+1)*
          (D+1)^3*(d+1)^3*(baseWidth 3 t+1)^2 := by
      gcongr
    have hc21 : s1 21=base 21 := by simp [s1]
    have hc26 : s1 26=base 26 := by simp [s1]
    rw [hc21,hc26] at hn2
    dsimp only [sourceRowBudget]
    omega

end SubexponentialSAT.SqrtLog.LayoutSourceRowsProgram

end OAI.Algorithms

import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutSourceRowsProgramAssembly
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutSourceRowsProgramRowsModel
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutSourceRowsProgramReadinessModel

namespace OAI.Algorithms

/-! Composition of the actual outer controller and the actual polynomial
executor. Only the concrete packed-source command contract is supplied by
the layout dispatcher; arithmetic and row traversal are fully discharged. -/
namespace SubexponentialSAT.SqrtLog.LayoutSourceRowsProgram
open SubexponentialSAT BitProgram StructuredCalls
open SubexponentialSAT.SubexpLiftRing SubexponentialSAT.SubexpQuarticRing
attribute [local simp] Fin.coe_ofNat_eq_mod

theorem sourceRows_present_model (t : ℕ) (ht : 0 < t) {d : ℕ} (hd : 0 < d)
    (a : RingModel.Data d) (M : SubexpPreparedQuartic.Modulus 3 t)
    (cache : RingProgram.ScalarCache 3 t) (hz : BinaryArithmetic.toNat cache.zero.val < 3^t)
    (R : ℕ) (width : List Bool) (frame : Fin 6 → List Bool)
    (source : Code) (s : Store) (v N f K L : ℕ) (ps : List (ℕ × ℕ))
    (value : ℕ → Polynomial (a.O t))
    (hinit : LayoutSourceRowsProgramInitialize.Ready (s ∘ initializationPorts)
      (R+1) (d*baseWidth 3 t))
    (hv : s 233=LayoutSourcePlanLookup.unary v)
    (hN : s 212=LayoutSourcePlanLookup.unary N)
    (hf : s 216=LayoutSourcePlanLookup.unary f)
    (hplan : s 337=LayoutOwnerFiberProgram.stream ps)
    (hmem : (v,N+f) ∈ ps)
    (hlookup : LayoutSourcePlanLookup.Native.Clean
      (⟨fun _ => false,initializeFinish s (R+1) (d*baseWidth 3 t)⟩ : Data))
    (hclean : RowsClean (preparedSourceStore s (R+1) (d*baseWidth 3 t) ps v N f)) (hwork : RowWorkClean (preparedSourceStore s (R+1) (d*baseWidth 3 t) ps v N f))
    (howner : ∀ i : Fin 11, 2 ≤ i.val → (preparedSourceStore s (R+1) (d*baseWidth 3 t) ps v N f) (ownerStacks i)=[])
    (H : DensePolynomialProgram.PairSpec.BaseReady 3 t M cache
      (HornerProgram.modelTable t a M cache) (s ∘ executorPorts) width frame)
    (E : LayoutSourceRowsProgramReadiness.Empty s)
    (hsource : ∀ j, j < N → ∀ remaining acc,
      RelSourceSpec source (rowState (preparedSourceStore s (R+1) (d*baseWidth 3 t) ps v N f) j remaining acc)
        (fun e : Algorithm.Expr (List (PolynomialExecutorProgram.Coeff (baseWidth 3 t) d)) =>
          SubexpPostfixControl.serializeCode DensePolynomialProgram.encode e.compile)
        (TypedSourceRel DensePolynomialProgram.encode
          (PolynomialExecutorProgram.meaning (RingProgram.modelRing t ht hd a M cache)) value L)
        (ps.length-1) K L)
    (hdegree : ∀ i, i < ps.length → (value i).natDegree ≤ R)
    (regs : Fin 16 → Bool) :
    ∃ rows n rf,
      RowProperty DensePolynomialProgram.encode
        (fun j out => PolynomialExecutorProgram.meaning (RingProgram.modelRing t ht hd a M cache) out=
          ownerSum ps j value) ((R+1)*(d*baseWidth 3 t)) 0 rows ∧ rows.length=N ∧
      n ≤ LayoutSourceRowsProgramInitialize.budget (R+1) (d*baseWidth 3 t)+
        LayoutSourcePlanLookup.pairBudget v N f ps+
        N*(uniformRowBudget N ps (ps.length-1) K L (R+1) d (baseWidth 3 t)
          ((preparedSourceStore s (R+1) (d*baseWidth 3 t) ps v N f) 21).length ((preparedSourceStore s (R+1) (d*baseWidth 3 t) ps v N f) 26).length+19*((R+1)*(d*baseWidth 3 t))+39)+
        2*(ps.idxOf (v,N+f))+23 ∧
      Eval (sourceRowsWith source) n (⟨regs,s⟩ : Data)
        (⟨rf,Function.update (initializeFinish s (R+1) (d*baseWidth 3 t)) 205
          (Encoding.encodeList DensePolynomialProgram.encode rows)⟩ : Data) := by
  let p := preparedSourceStore s (R+1) (d*baseWidth 3 t) ps v N f
  have Hready := LayoutSourceRowsProgramReadiness.model_ready_of_low_agreement
    t a M cache hz s p (R+1) width frame H E (by
      intro i hi
      have hn : i≠304 := by intro he; subst i; norm_num at hi
      simp [p,preparedSourceStore,hn])
  have hsp : p 337=LayoutOwnerFiberProgram.stream ps := by
    simpa [p,preparedSourceStore,initializeFinish] using hplan
  have hids : ∀ j, j < N → ∀ i∈LayoutOwnerFiberProgram.fiberIndices j 0 ps,
      i ≤ ps.length-1 := by
    intro j hj i hi
    have hl := LayoutOwnerFiberProgram.mem_fiberIndices_lt j ps hi
    omega
  have hrs := sourceRows_relSpec t ht hd a M cache hz (R+1) width frame
    source p (ps.length-1) K L N ps (fun _ => value) hsource hsp howner hwork hids Hready
  have hrfull : RelRowSpec (sourceRowWith source) p DensePolynomialProgram.encode
      (fun j out => PolynomialExecutorProgram.meaning (RingProgram.modelRing t ht hd a M cache) out=
        ownerSum ps j value) N
      (uniformRowBudget N ps (ps.length-1) K L (R+1) d (baseWidth 3 t)
        (p 21).length (p 26).length) ((R+1)*(d*baseWidth 3 t)) := by
    intro j hj remaining acc rr
    obtain ⟨out,n,rf,hm,hl,hn,he⟩ := hrs j hj remaining acc rr
    refine ⟨out,n,rf,?_,hl,hn,he⟩
    rw [ownerSum_full_degree ps j value R (by
      intro i hi
      exact hdegree i (LayoutOwnerFiberProgram.mem_fiberIndices_lt j ps hi))] at hm
    exact hm
  exact sourceRows_present_from_rows source s (R+1) (d*baseWidth 3 t) v N f ps
    hinit hv hN hf hplan hmem hlookup DensePolynomialProgram.encode _ _ _ hrfull hclean regs

end SubexponentialSAT.SqrtLog.LayoutSourceRowsProgram

end OAI.Algorithms

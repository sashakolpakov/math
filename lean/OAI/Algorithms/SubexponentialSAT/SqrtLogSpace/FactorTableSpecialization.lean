import OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FactorTableProgram
import OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryIncidenceSpace

/-! Proof-side correctness of the unchanged immediately specialized incidence
call. Operational command definitions remain in FactorTableProgram. -/
namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FactorTableProgram
open OAI.Algorithms.SubexponentialSAT.SqrtLog
open OAI BitProgram StructuredCalls SubexpConvolutionControl SubexpScanPrimitives
open SubexpPolynomialConstructor PerturbationAssembly OAI.Algorithms.SubexponentialSAT.SubexpLiftRing

attribute [local simp] Fin.coe_ofNat_eq_mod

def specializeBudget (t d u J N n count rawLength : ℕ)
    (low : Fin 256 → List Bool) : ℕ :=
  QueryProducerSpace.Native.combinedBudget
    (PerturbationAssembly.lowWorkPolynomial n N J t d
      ((low 192).length + (low 193).length + (low 243).length))
    ((low 194).length + (low 202).length + (low 204).length)
    rawLength n (baseWidth 3 t) d u J count

/-- Input words alone instantiate the concrete emitter/specializer. The result
has empty correction support before its bytes enter the outer lookup table. -/
theorem specializeCall_run (t : ℕ) (ht : 0 < t) {d : ℕ} (hd : 0 < d)
    (model : RingModel.Data d) (M : SubexpPreparedQuartic.Modulus 3 t)
    (cache : RingProgram.ScalarCache 3 t) (u J N : ℕ) (hu : 0 < u) (hJ : 0 < J)
    (theta : DensePolynomialProgram.Coeff (baseWidth 3 t) d)
    (rows : List (DensePolynomialProgram.Fixed.Array (baseWidth 3 t) d N × Bool))
    (a : OuterData) (low : Fin 256 → List Bool)
    (hinput : PerturbationAssembly.LowInput t model M cache J N theta rows low)
    (hout : low 217 = []) (U : Finset (Fin rows.length))
    (hmask : a.stacks 857 = Squarefree.encodeMask U) (htmp : a.stacks 881 = [])
    (hs : ∀ i, a.stacks (joinedPort i) =
      (QueryProducerSpace.Native.joinedState a.regs low
        (QueryProducerSpace.Native.emptyHigh [])).stacks i) :
    let source := QueryProducerSpace.emittedSource t model M cache J N theta rows
    let result := MomentsProgram.Normalize.run 3 t M cache
      (HeadEvaluation.specializeEntries U source) []
    ∃ k rf, k ≤ 7*(a.stacks 857).length+5+
      specializeBudget t d u J N rows.length (1+rows.length*(J-1))
        (MomentsProgram.Product.bytes source).length low ∧
      TruncatedRingProgram.Good ∅ u J result ∧
      Eval specializeCall k a
        (⟨rf, Function.update a.stacks 557 (MomentsProgram.Product.bytes result)⟩ : OuterData) := by
  dsimp only
  let copied := SubexpSetupStorage.copyState 857 625 a
  let source := QueryProducerSpace.emittedSource t model M cache J N theta rows
  let result := MomentsProgram.Normalize.run 3 t M cache
    (HeadEvaluation.specializeEntries U source) []
  obtain ⟨steps, rr, hsteps, hrun, hgood, _⟩ :=
    QueryProducerSpace.Native.run_space t ht hd model M cache u J N hu hJ theta rows
      low hinput hout copied.regs U
  have hshape := copied_joined_shape a low hs
  rw [hmask] at hshape
  have htrace : Trace QueryProducerSpace.Native.program steps
      ((projectState id joinedPort copied).withPC
        (some QueryProducerSpace.Native.program.entry))
      ((QueryProducerSpace.Native.joinedState rr
        (Function.update low 217 (MomentsProgram.Product.bytes result))
        (QueryProducerSpace.Native.emptyHigh [])).withPC none) := by
    rw [hshape]
    exact hrun
  have hp := eval_call_from_state QueryProducerSpace.Native.program id joinedPort copied
    Function.injective_id joinedPort_injective htrace
  have ho := specialized_joined_output a low rr (MomentsProgram.Product.bytes result) hs
  rw [ho] at hp
  have hc := SubexpSetupStorage.copy_eval 857 625 881 a
    (by decide) (by decide) (by decide) htmp
  refine ⟨7*(a.stacks 857).length+5+steps, rr, ?_, hgood, hc.seq hp⟩
  exact Nat.add_le_add_left hsteps _

/-- The native high-variable branch already has empty correction support.
Both cutoff positivity facts are provided by the actual parameter choice. -/
theorem high_payload_good {n B d : ℕ} (u J : ℕ) (hu : 0 < u) (hJ : 0 < J)
    (c : RingProgram.Code (OAI.Algorithms.SubexponentialSAT.SubexpQuarticRing.Word B) d) :
    ∃ entries : List (MomentsProgram.Product.Entry n B d),
      TruncatedRingProgram.Good ∅ u J entries ∧
      Encoding.frame (originKey n) ++ Encoding.frame (RingProgram.flat c) =
        MomentsProgram.Product.bytes entries := by
  refine ⟨Squarefree.Sparse.constant u J c, TruncatedRingProgram.constant_good u J c, ?_⟩
  have h := PerturbationAssembly.origin_dictionary n c
  rw [QueryProducerSpace.dictionaryBits_productBytes] at h
  simpa [Squarefree.Sparse.constant, hu, hJ] using h

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FactorTableProgram

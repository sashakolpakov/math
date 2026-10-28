import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SubexpTaylorProgram
import OAI.Algorithms.SubexponentialSAT.SubexpTaylorCacheSemantics
import OAI.Algorithms.SubexponentialSAT.SubexpTaylorRowFrames

namespace OAI.Algorithms

/-! A complete physical Taylor-row producer. The input row is the reversed
payload returned by the record parser. The program shifts the entire row,
frames the requested low coefficients, and clears the unused high tail. -/

namespace SubexponentialSAT.SubexpTaylorRow

open BitProgram StructuredCalls SubexpScanPrimitives SubexpHornerControl
open SubexpTaylorControl SubexpLiftRing SubexpQuarticRing

abbrev shift : Cmd 8 90 :=
  .call (ProgramLinking.liftProgram SubexpTaylorProgram.reversedShiftProgram id shiftPorts)
abbrev command : Cmd 8 90 := .seq shift (.seq frame clear)
abbrev program : Program 8 90 (size command + 1) := compiled command 87 89

def budget (n N B : ℕ) : ℕ :=
  n * ((n + 1) * (SubexpTaylorProgram.scalarBound B + 33 * (4 * B) + 27) + 2) + 3 +
    (N * (28 * (4 * B) + 33) + 11) + (2 * (n * (4 * B)) + 3) + 1

variable (p μ : ℕ) [Fact p.Prime] (M : SubexpPreparedQuartic.Modulus p μ)

abbrev Code := Quad (Word (baseWidth p μ))
abbrev flat := @SubexpQuarticFlatMul.flat

def cache (t theta : Code p μ) (N : ℕ) (P : List (Code p μ)) : List (Code p μ) :=
  SubexpTaylorCacheSemantics.retain (SubexpHornerMachine.zeroCode p μ) N
    (SubexpTaylorSemantics.compactShift (SubexpHornerMachine.stepValue p μ M t theta) P)

omit [Fact p.Prime] in
@[simp] theorem cache_length (t theta : Code p μ) (N : ℕ) (P : List (Code p μ)) :
    (cache p μ M t theta N P).length = N := by
  exact SubexpTaylorCacheSemantics.retain_length _ _ _

omit [Fact p.Prime] in
/-- The physical ordered list is exactly the finite Taylor array consumed
by the incidence-argument serializer. -/
theorem cache_eq_ofFn_getD (t theta : Code p μ) (N : ℕ) (P : List (Code p μ)) :
    cache p μ M t theta N P = List.ofFn (fun j : Fin N =>
      (cache p μ M t theta N P).getD j.val (SubexpHornerMachine.zeroCode p μ)) := by
  apply List.ext_getElem
  · simp
  · intro j hj hj'
    rw [List.getElem_ofFn]
    exact (List.getD_eq_getElem _ _ hj).symm

omit [Fact p.Prime] in
theorem encode_length (P : List (Code p μ)) :
    (Encoding.encodeList flat P).length = (8 * baseWidth p μ + 2) * P.length + 1 := by
  induction P with
  | nil => simp [Encoding.encodeList]
  | cons a P ih =>
      simp only [Encoding.encodeList, List.length_cons, List.length_append,
        Encoding.length_frame, SubexpQuarticFlatMul.flat_length, ih]
      ring

omit [Fact p.Prime] in
theorem cache_encode_length (t theta : Code p μ) (N : ℕ) (P : List (Code p μ)) :
    (Encoding.encodeList flat (cache p μ M t theta N P)).length =
      (8 * baseWidth p μ + 2) * N + 1 := by
  rw [encode_length, cache_length]

theorem encode_map {C : Type*} (encode : C → List Bool) (P : List C) :
    Encoding.encodeList id (P.map encode) = Encoding.encodeList encode P := by
  induction P with
  | nil => rfl
  | cons a P ih => simp [Encoding.encodeList, ih]

theorem program_trace (hμ : 0 < μ) (t theta : Code p μ)
    (width blockWidth : List Bool) (hw : width.length = baseWidth p μ)
    (hblock : blockWidth.length = 4 * baseWidth p μ)
    (N : ℕ) (P : List (Code p μ)) (regs : Fin 8 → Bool) :
    ∃ n ≤ budget P.length N (baseWidth p μ), ∃ regs',
      Trace program n
        ((rowState regs (done (SubexpHornerMachine.baseWords p μ M t theta width blockWidth) [])
          (encodeList flat P).reverse (List.replicate N true) []).withPC (some program.entry))
        ((rowState regs' (done (SubexpHornerMachine.baseWords p μ M t theta width blockWidth) [])
          [] [] (Encoding.encodeList flat (cache p μ M t theta N P))).withPC none) := by
  let base := SubexpHornerMachine.baseWords p μ M t theta width blockWidth
  let Q := SubexpTaylorSemantics.compactShift (SubexpHornerMachine.stepValue p μ M t theta) P
  let output := Encoding.encodeList id (SubexpTaylorFrames.chunks blockWidth.length N (encodeList flat Q))
  obtain ⟨ns, hns, rs, hs⟩ := SubexpTaylorProgram.reversed_shift_trace p μ M hμ
    t theta width blockWidth hw hblock regs P
  have hshift := eval_call_lifted SubexpTaylorProgram.reversedShiftProgram id shiftPorts
    (rowState regs (done base []) (encodeList flat P).reverse (List.replicate N true) [])
    Function.injective_id shiftPorts.injective hs
  have hshift' : Eval shift ns
      (rowState regs (done base []) (encodeList flat P).reverse (List.replicate N true) [])
      (rowState rs (done base (encodeList flat Q)) [] (List.replicate N true) []) := by
    simpa only [shift, embed_shift, base, Q] using hshift
  obtain ⟨rf, hf⟩ := frame_eval rs base (encodeList flat Q) N
  have hc := clear_eval (mergeRegs rs rf) base
    ((encodeList flat Q).drop (N * blockWidth.length)) output
  have he := hshift'.seq (hf.seq hc)
  have hlen : (encodeList flat Q).length = P.length * (4 * baseWidth p μ) := by
    rw [SubexpTaylorOuter.encodeList_length flat (4 * baseWidth p μ)
      SubexpQuarticFlatMul.flat_length, SubexpTaylorSemantics.compactShift_length]
  have hout : output = Encoding.encodeList flat (cache p μ M t theta N P) := by
    dsimp [output]
    rw [hblock, SubexpTaylorCacheSemantics.chunks_encode flat
      (SubexpHornerMachine.zeroCode p μ) (4 * baseWidth p μ)
      SubexpQuarticFlatMul.flat_length (SubexpHornerMachine.zeroCode_flat p μ)]
    rw [encode_map]
    rfl
  refine ⟨ns + (N * (28 * base.blockWidth.length + 33) + 11 +
      (2 * ((encodeList flat Q).drop (N * blockWidth.length)).length + 3)) + 1, ?_,
    readRegs (mergeRegs rs rf) 0 1 none, ?_⟩
  · have hdrop : ((encodeList flat Q).drop (N * blockWidth.length)).length ≤
        P.length * (4 * baseWidth p μ) := by
      rw [List.length_drop, hlen]
      exact Nat.sub_le _ _
    dsimp [base, SubexpHornerMachine.baseWords]
    rw [hblock]
    rw [hblock] at hdrop
    unfold budget
    omega
  · simpa only [command, base, hout] using compiled_halt_trace he 87 89

theorem cache_coeff (c : Fin 4 → ZMod (p^μ)) (t theta : Code p μ)
    (ht : t.map (wordValue p μ) = reductionData c)
    (N : ℕ) (P : List (Code p μ)) (j : ℕ) (hj : j < N) :
    SubexpHornerMachine.decode p μ c
      ((cache p μ M t theta N P).getD j (SubexpHornerMachine.zeroCode p μ)) =
      ((PolynomialAlgorithm.denote (P.map (SubexpHornerMachine.decode p μ c))).comp
        (Polynomial.X + Polynomial.C (SubexpHornerMachine.decode p μ c theta))).coeff j := by
  exact SubexpTaylorCacheSemantics.shifted_cache_coeff
    (SubexpHornerMachine.decode p μ c) (SubexpHornerMachine.zeroCode p μ)
    (SubexpHornerMachine.zeroCode_decode p μ c)
    (SubexpHornerMachine.stepValue p μ M t theta) (SubexpHornerMachine.decode p μ c theta)
    (by
      intro a b
      simp only [SubexpHornerMachine.stepValue, SubexpHornerMachine.decode,
        SubexpPreparedQuartic.binaryAdd_quotient,
        SubexpPreparedQuartic.binaryMul_quotient p μ M c t a theta ht]) N P j hj

end SubexponentialSAT.SubexpTaylorRow

end OAI.Algorithms

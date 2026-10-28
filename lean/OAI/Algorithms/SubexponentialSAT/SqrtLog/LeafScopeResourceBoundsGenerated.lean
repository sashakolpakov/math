import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafScopeResourceBoundsDecode
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafScopeResourceBoundsUniform

namespace OAI.Algorithms

/-! Concrete generated-queue and supplied-table instantiation. The framed
bitstream is proved equal to the exact raw table consumed by the scope stage. -/
namespace SubexponentialSAT.SqrtLog.LeafScopeResourceBounds
open Asymptotic HashSelectProgram LeafStatisticsProgram

theorem selected_mem (score : Records → List Bool → List Bool)
    (seed : List Bool) (rest initial : Records) (round : ℕ) (p : List Bool)
    (hp : p ∈ selected score seed rest initial round) : p ∈ seed :: rest ∨ p ∈ initial := by
  induction round with
  | zero => exact Or.inr hp
  | succ round ih =>
    simp only [selected, iter_succ_apply, payloadNext, List.mem_cons] at hp
    rcases hp with rfl | hp
    · exact Or.inl (HashSelect.best_mem _ seed rest)
    · exact ih hp

theorem raw_records_encoding {m width : ℕ} (hm : 0 < m) (records : Records)
    (h : ∀ p ∈ records, (CodeRowsProgram.rowPayload width m (rawDecode m width hm p)).reverse = p) :
    candidateEncoding records = Encoding.encodeList (CodeRowsProgram.rowPayload width m)
      (records.map (rawDecode m width hm)) := by
  induction records with
  | nil => rfl
  | cons p ps ih =>
    have hh : p.reverse = CodeRowsProgram.rowPayload width m (rawDecode m width hm p) := by
      simpa only [List.reverse_reverse] using (congrArg List.reverse (h p (by simp))).symm
    have ht := ih (fun p hp => h p (by simp [hp]))
    simp only [candidateEncoding, Encoding.encodeList, List.map_cons, hh, ht]

/-- All decoder premises in `supplied_trial_measured` are discharged for the
actual generated alphabet and the supplied initial code-row stream. -/
theorem generated_trial_measured (n B t d k q round : ℕ) (clauses : List (List Bool))
    (codes : Fin clauses.length → List ℕ) (hcodes : ∀ i, (codes i).length ≤ k)
    (s : SparseCode.SuppliedShifts clauses.length B)
    (Q : SparseCode.SuppliedLocal clauses.length B)
    (countWord : List Bool) (hcountWord : CounterPrograms.value countWord = 3*clauses.length)
    (score : Records → List Bool → List Bool) (seed : List Bool) (rest : Records)
    (hfamily : generatedPayloads (SubexpAlphabetProgram.alphabetWords countWord)
      (SparseCode.distanceDenom clauses.length B) = seed :: rest)
    (bits : List Bool) (hb : bits ∈ seed :: rest) (mark : Option (Fin clauses.length))
    (hn : 0 < n) (hm : 0 < clauses.length) (hB : 0 < B) (hmb : clauses.length ≤ n * B)
    (hBL : B ≤ L n^q) (hsize : Nat.size clauses.length ≤ n)
    (hr : round ≤ HashSelect.loopCap n clauses.length)
    (nb tb : List Bool) (hnb : BinaryArithmetic.toNat nb = n)
    (htb : BinaryArithmetic.toNat tb = Nat.sqrt (L n)+1) :
    let initial := initialPayloads countWord.length (CodeRowsProgram.serializedRows clauses.length s Q)
    let decode := rawDecode clauses.length countWord.length hm
    let rows := trial decode score seed rest initial round bits
    let scopes := HashScopeProgram.Complete.scopes t d codes rows mark
    let mask := forwardMask scopes (HighIncidenceProgram.Prepare.cut scopes nb tb) n
    candidateEncoding (bits :: selected score seed rest initial round) =
      Encoding.encodeList (CodeRowsProgram.rowPayload countWord.length clauses.length) rows ∧
    (measured scopes mask).occurrence ≤ statCoefficient k q * L n^resourceExponent q ∧
    max (Arity.arity mask scopes 0) (if (measured scopes mask).uncovered=0 then 0 else 1) ≤
      statCoefficient k q * L n^resourceExponent q ∧
    scopes.length + (measured scopes mask).uncovered ≤ 4*n + HashSelect.loopCap n clauses.length+2 ∧
    slots scopes ≤ n*(massCoefficient k q*L n^(2*q+3)) ∧
    (measured scopes mask).incidences ≤ n*(massCoefficient k q*L n^(2*q+3)+1) ∧
    (∀ row ∈ scopes, row.Nodup) ∧ mask.length=n := by
  let initial := initialPayloads countWord.length (CodeRowsProgram.serializedRows clauses.length s Q)
  have hw : 3*clauses.length ≤ 2^countWord.length :=
    (HashFamilyPayload.countWord_width_sufficient countWord hcountWord).le
  have hf : generatedPayloads (HashFamilyPayload.alphabet clauses.length countWord.length)
      (SparseCode.distanceDenom clauses.length B) = seed :: rest := by
    simpa only [HashFamilyPayload.alphabetWords_eq countWord hcountWord] using hfamily
  have hlength : ∀ p ∈ seed :: rest,
      (rawDecode clauses.length countWord.length hm p).length ≤ SparseCode.distanceDenom clauses.length B := by
    intro p hp
    rw [rawDecode_generated_length (depth := SparseCode.distanceDenom clauses.length B) hm hw p (by simpa [hf] using hp)]
  have hdecode := initialPayloads_decode hm hw (CodeRowsProgram.serializedRows clauses.length s Q)
  refine ⟨?_, supplied_trial_measured n B t d k q round clauses codes hcodes s Q
    (rawDecode clauses.length countWord.length hm) score seed rest initial hdecode hlength
    bits hb mark hn hm hB hmb hBL hsize hr nb tb hnb htb⟩
  apply raw_records_encoding
  intro p hp
  simp only [List.mem_cons] at hp
  have hp' : p ∈ seed :: rest ∨ p ∈ initial := hp.elim
    (fun he => Or.inl (he.symm ▸ hb)) (selected_mem score seed rest initial round p)
  rcases hp' with hp | hp
  · exact rawDecode_generated_payload (depth := SparseCode.distanceDenom clauses.length B) hm hw p (by simpa [hf] using hp)
  · obtain ⟨row,hrow,rfl⟩ := List.mem_map.mp hp
    rw [rawDecode_rowPayload hm hw]

end SubexponentialSAT.SqrtLog.LeafScopeResourceBounds

end OAI.Algorithms

import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.HashSelectProgramBounded

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.HashSelectProgram

open SubexponentialSAT.Subexp

/-- Argmin only inspects the scores of actual candidates. -/
theorem best_congr_on {P : Type*} (f g : P → ℕ) (seed : P) (rest : List P)
    (h : ∀ p ∈ seed :: rest, f p = g p) :
    HashSelect.best f seed rest = HashSelect.best g seed rest := by
  induction rest generalizing seed with
  | nil => rfl
  | cons a rest ih =>
    have hs := h seed (by simp)
    have ha := h a (by simp)
    simp only [HashSelect.best, hs, ha]
    split_ifs
    · exact ih a (fun p hp => h p (by simp only [List.mem_cons] at hp ⊢; tauto))
    · exact ih seed (fun p hp => h p (by simp only [List.mem_cons] at hp ⊢; tauto))

theorem payloadNext_decode {R : Type*} (evaluate : List R → ℕ) (decode : List Bool → R)
    (score : Records → List Bool → List Bool) (seed : List Bool) (rest rows : Records)
    (hs : ∀ bits ∈ seed :: rest,
      BinaryArithmetic.toNat (score rows bits) = evaluate (decode bits :: rows.map decode)) :
    (payloadNext score seed rest rows).map decode =
      HashSelect.listStep evaluate decode seed rest (rows.map decode) := by
  have h := best_congr_on (fun bits => BinaryArithmetic.toNat (score rows bits))
    (fun bits => evaluate (decode bits :: rows.map decode)) seed rest hs
  simp only [payloadNext, List.map_cons, HashSelect.listStep, h]

/-- On the actual iterates, the finite controller implements the semantic
list-based greedy selector exactly. Only tested payloads require exactness. -/
theorem iter_decode {R : Type*} (evaluate : List R → ℕ) (decode : List Bool → R)
    (score : Records → List Bool → List Bool) (seed : List Bool) (rest rows : Records) (K : ℕ)
    (hs : ∀ t < K, ∀ bits ∈ seed :: rest,
      BinaryArithmetic.toNat (score (iter (payloadNext score seed rest) t rows) bits) =
        evaluate (decode bits :: (iter (payloadNext score seed rest) t rows).map decode)) :
    (iter (payloadNext score seed rest) K rows).map decode =
      HashSelect.listRun evaluate decode seed rest (rows.map decode) K := by
  induction K with
  | zero => rfl
  | succ K ih =>
    rw [iter_succ_apply, payloadNext_decode evaluate decode score seed rest _ (hs K (by omega)),
      ih (fun t ht => hs t (by omega))]
    rfl

end SubexponentialSAT.SqrtLog.HashSelectProgram

end OAI.Algorithms

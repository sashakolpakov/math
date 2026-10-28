import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.ReconstructionProgramMiddle
import OAI.Algorithms.SubexponentialSAT.SubexpCRTAtZero

namespace OAI.Algorithms

/-! Algebraic interpretation of the values produced by the physical outer
Hermite stages. This uses precisely the coefficient list evaluated by the
native Horner loop. -/
namespace SubexponentialSAT.SqrtLog.ReconstructionProgram.Middle

open SubexponentialSAT Polynomial
open scoped BigOperators

variable {C A : Type*} [CommRing A]

theorem factor_decode (decode : C → A) (mul : C → C → C)
    (hm : ∀ a b, decode (mul a b) = decode a * decode b)
    (minusOne unit : C) (hminus : decode minusOne = -1) (hu : decode unit = 1)
    (J : ℕ) (cs : List C) :
    decode (cs.foldl (Cofactor.includeValue mul minusOne J) unit) =
      (cs.map (fun c => (-decode c)^J)).prod := by
  have hf (a : C) : decode (cs.foldl (Cofactor.includeValue mul minusOne J) a) =
      decode a * (cs.map (fun c => (-decode c)^J)).prod := by
    induction cs generalizing a with
    | nil => simp
    | cons c cs ih =>
      rw [List.foldl_cons, ih, Cofactor.includeValue_decode decode mul hm minusOne hminus]
      simp [mul_assoc]
  rw [hf, hu, one_mul]

theorem nodeValue_decode (decode : C → A) (mul add : C → C → C)
    (hm : ∀ a b, decode (mul a b) = decode a * decode b)
    (ha : ∀ a b, decode (add a b) = decode a + decode b)
    (minusOne zero unit node acc : C)
    (hminus : decode minusOne = -1) (hz : decode zero = 0) (hu : decode unit = 1)
    (J : ℕ) (remaining processed correction : List C) :
    decode (nodeValue mul add minusOne zero unit node acc J remaining processed correction) =
      decode acc + ((remaining ++ processed).map (fun c => (-decode c)^J)).prod *
        (PolynomialAlgorithm.denote (correction.map decode)).eval (-decode node) := by
  unfold nodeValue
  rw [ha, hm, factor_decode decode mul hm minusOne unit hminus hu,
    HornerProgram.output_decode decode mul add hm ha correction _ zero hz, hm, hminus]
  simp

theorem indexed_nodeValue_decode {Q : ℕ}
    (decode : C → A) (mul add : C → C → C)
    (hm : ∀ a b, decode (mul a b) = decode a * decode b)
    (ha : ∀ a b, decode (add a b) = decode a + decode b)
    (minusOne zero unit acc : C)
    (hminus : decode minusOne = -1) (hz : decode zero = 0) (hu : decode unit = 1)
    (nodes : Fin Q → C) (J : ℕ) (remaining processed : List (Fin Q)) (i : Fin Q)
    (hfull : List.finRange Q = processed.reverse ++ i :: remaining)
    (correction : List C) (H : A[X])
    (hc : PolynomialAlgorithm.denote (correction.map decode) = H) :
    decode (nodeValue mul add minusOne zero unit (nodes i) acc J
      (remaining.map nodes) (processed.map nodes) correction) =
      decode acc + (JetCRT.cofactor (decode ∘ nodes) J i).eval 0 * H.eval (-decode (nodes i)) := by
  rw [nodeValue_decode decode mul add hm ha _ _ _ _ _ hminus hz hu, hc,
    SubexpCRTAtZero.cofactor_eval_zero]
  congr 2
  simpa only [← List.map_append, List.map_map, Function.comp_def] using
    SubexpCRTOuterProgram.cofactor_stream_product processed remaining i
      (fun j => (-decode (nodes j))^J) hfull

/-- The semantic target of the native node contributions is the ordinary
Hermite reconstruction, with no full reconstructed polynomial materialized. -/
theorem sum_node_terms {Q : ℕ} (theta : Fin Q → A) (J : ℕ)
    (inverse : Fin Q → A) (jets : Fin Q → A[X]) :
    ((List.finRange Q).map (fun i => (JetCRT.cofactor theta J i).eval 0 *
      (TruncatedInverse.correction theta J inverse jets i).eval (-theta i))).sum =
      SubexpCRTAtZero.value theta J inverse jets := by
  rw [← List.ofFn_eq_map, List.sum_ofFn]
  rfl

end SubexponentialSAT.SqrtLog.ReconstructionProgram.Middle

end OAI.Algorithms

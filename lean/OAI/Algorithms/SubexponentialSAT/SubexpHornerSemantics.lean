import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SubexpHornerControl
import OAI.Algorithms.SubexponentialSAT.SubexpPreparedQuartic
import OAI.Algorithms.SubexponentialSAT.PolynomialAlgorithm

namespace OAI.Algorithms

namespace SubexponentialSAT.SubexpHornerMachine

open SubexpHornerControl SubexpQuarticRing

variable (p μ : ℕ) [Fact p.Prime] (M : SubexpPreparedQuartic.Modulus p μ)

def stepValue (t x a c : Quad (Word (SubexpLiftRing.baseWidth p μ))) :
    Quad (Word (SubexpLiftRing.baseWidth p μ)) :=
  (SubexpPreparedQuartic.binaryAdd p μ M
    (SubexpPreparedQuartic.binaryMul p μ M t a x).1 c).1

noncomputable def decode (c : Fin 4 → ZMod (p^μ))
    (a : Quad (Word (SubexpLiftRing.baseWidth p μ))) := quotientDenote c (a.map (wordValue p μ))

theorem fold_decode (c : Fin 4 → ZMod (p^μ))
    (t x : Quad (Word (SubexpLiftRing.baseWidth p μ)))
    (ht : t.map (wordValue p μ) = reductionData c)
    (cs : List (Quad (Word (SubexpLiftRing.baseWidth p μ))))
    (a : Quad (Word (SubexpLiftRing.baseWidth p μ))) :
    decode p μ c (fold (stepValue p μ M t x) cs a) =
      cs.foldl (fun value b => value * decode p μ c x + decode p μ c b) (decode p μ c a) := by
  induction cs generalizing a with
  | nil => rfl
  | cons b cs ih =>
      change decode p μ c (fold (stepValue p μ M t x) cs (stepValue p μ M t x a b)) = _
      rw [ih, List.foldl_cons]
      simp only [stepValue, decode,
        SubexpPreparedQuartic.binaryAdd_quotient,
        SubexpPreparedQuartic.binaryMul_quotient p μ M c t _ x ht]

/-- Semantic endpoint for a seed representing zero. -/
theorem output_decode (c : Fin 4 → ZMod (p^μ))
    (t x : Quad (Word (SubexpLiftRing.baseWidth p μ)))
    (ht : t.map (wordValue p μ) = reductionData c)
    (P : List (Quad (Word (SubexpLiftRing.baseWidth p μ))))
    (zero : Quad (Word (SubexpLiftRing.baseWidth p μ)))
    (hz : decode p μ c zero = 0) :
    decode p μ c (fold (stepValue p μ M t x) P.reverse zero) =
      (PolynomialAlgorithm.denote (P.map (decode p μ c))).eval (decode p μ c x) := by
  rw [fold_decode p μ M c t x ht, List.foldl_reverse, hz]
  induction P with
  | nil => simp []
  | cons a P ih =>
      simp [ ih, add_comm, mul_comm]

end SubexponentialSAT.SubexpHornerMachine

end OAI.Algorithms

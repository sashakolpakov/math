import OAI.NumberTheory.PadicHodge.IntegralComparison.Quotient.RingFlatness
import OAI.NumberTheory.PadicHodge.IntegralComparison.SmoothWitt.FrameForms

/-! # Frame Flatness -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.SmoothWitt.FrameFlatness

noncomputable section

/-! Each actual smooth Witt frame is flat over its original truncated Witt coefficient ring. -/

universe u

variable (p : ℕ) [Fact p.Prime] (k A : Type u) [Field k]
  [CommRing A] [Algebra (WittVector p k) A] [Module.Flat (WittVector p k) A] (n : ℕ)

local notation "W" => WittVector p k

def base : (W ⧸ (Ideal.span {(p : W)}) ^ (n + 1)) →+* FrameRing.Ring p A n :=
  IntegralComparison.Quotient.RingFlatness.map W A ((Ideal.span {(p : W)}) ^ (n + 1))
    ((Ideal.span {(p : A)}) ^ (n + 1)) (FrameForms.powerIdeal_eq p k A n)

omit [Module.Flat W A] in
theorem base_mk (w : W) : base p k A n
    (Ideal.Quotient.mk ((Ideal.span {(p : W)}) ^ (n + 1)) w) = FrameRing.base p k A n w := rfl

theorem flat : (base p k A n).Flat :=
  IntegralComparison.Quotient.RingFlatness.flat W A ((Ideal.span {(p : W)}) ^ (n + 1))
    ((Ideal.span {(p : A)}) ^ (n + 1)) (FrameForms.powerIdeal_eq p k A n)

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.SmoothWitt.FrameFlatness

import Mathlib

/-! # Quotient Section -/

namespace OAI.RepresentationTheory.Theta.Adelic.QuotientSection

noncomputable section

/-! Continuous sections descend to the actual quotient of a bundle
once their graph respects the base and bundle equivalence relations. -/

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]

def quotientProjection (R : Setoid X) (S : Setoid (X × Y))
    (hp : ∀ p q, S.r p q → R.r p.1 q.1) : Quotient S → Quotient R :=
  Quotient.lift (fun p => Quotient.mk R p.1) (fun p q h => Quotient.sound (hp p q h))

theorem quotientProjection_continuous (R : Setoid X) (S : Setoid (X × Y))
    (hp : ∀ p q, S.r p q → R.r p.1 q.1) : Continuous (quotientProjection R S hp) :=
  (continuous_quotient_mk'.comp continuous_fst).quotient_lift _

def descendedSection (R : Setoid X) (S : Setoid (X × Y)) (t : X → Y)
    (ht : ∀ x y, R.r x y → S.r (x, t x) (y, t y)) : Quotient R → Quotient S :=
  Quotient.lift (fun x => Quotient.mk S (x, t x)) (fun x y h => Quotient.sound (ht x y h))

theorem descendedSection_continuous (R : Setoid X) (S : Setoid (X × Y)) (t : X → Y)
    (ht : ∀ x y, R.r x y → S.r (x, t x) (y, t y)) (hc : Continuous t) :
    Continuous (descendedSection R S t ht) :=
  (continuous_quotient_mk'.comp (continuous_id.prodMk hc)).quotient_lift _

omit [TopologicalSpace X] [TopologicalSpace Y] in
theorem quotientProjection_descendedSection (R : Setoid X) (S : Setoid (X × Y))
    (hp : ∀ p q, S.r p q → R.r p.1 q.1) (t : X → Y)
    (ht : ∀ x y, R.r x y → S.r (x, t x) (y, t y)) (q : Quotient R) :
    quotientProjection R S hp (descendedSection R S t ht q) = q := by
  induction q using Quotient.inductionOn with
  | h x => rfl

end

end OAI.RepresentationTheory.Theta.Adelic.QuotientSection

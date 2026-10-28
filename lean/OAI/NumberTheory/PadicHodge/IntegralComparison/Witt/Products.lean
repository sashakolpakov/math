import OAI.NumberTheory.PadicHodge.PeriodInvariants.WittAlgebraFunctor

/-! # Products -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Witt.Products

noncomputable section

/-! Actual Witt vectors preserve products, coefficient by coefficient. -/

attribute [local instance] PeriodInvariants.WittAlgebraFunctor.wittAlgebra

variable (p : ℕ) [Fact p.Prime] {ι : Type*} (A : ι → Type*) [∀ i, CommRing (A i)]

def map : WittVector p (∀ i, A i) →+* ∀ i, WittVector p (A i) where
  toFun w i := WittVector.map (Pi.evalRingHom A i) w
  map_one' := funext fun i => (WittVector.map (Pi.evalRingHom A i)).map_one
  map_mul' x y := funext fun i => (WittVector.map (Pi.evalRingHom A i)).map_mul x y
  map_zero' := funext fun i => (WittVector.map (Pi.evalRingHom A i)).map_zero
  map_add' x y := funext fun i => (WittVector.map (Pi.evalRingHom A i)).map_add x y

theorem bijective : Function.Bijective (Products.map p A) := by
  constructor
  · intro x y h
    apply WittVector.ext
    intro n
    funext i
    exact congrArg (fun w => (w i).coeff n) h
  · intro v
    refine ⟨WittVector.mk p (fun n i => (v i).coeff n), ?_⟩
    funext i
    apply WittVector.ext
    intro n
    rfl

def ringEquiv : WittVector p (∀ i, A i) ≃+* ∀ i, WittVector p (A i) :=
  RingEquiv.ofBijective (Products.map p A) (bijective p A)

variable (R : Type*) [CommRing R] [∀ i, Algebra R (A i)]

def algebraEquiv : WittVector p (∀ i, A i) ≃ₐ[WittVector p R] ∀ i, WittVector p (A i) where
  __ := ringEquiv p A
  commutes' w := by
    funext i
    apply WittVector.ext
    intro n
    rfl

theorem coeff (w : WittVector p (∀ i, A i)) (i : ι) (n : ℕ) :
    (algebraEquiv p A R w i).coeff n = w.coeff n i := rfl

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Witt.Products

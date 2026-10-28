import Mathlib.RingTheory.DividedPowers.DPMorphism
import Mathlib.Algebra.Category.Ring.Basic
import Mathlib.Algebra.Ring.TransferInstance
import Mathlib.Algebra.Ring.Pi
import Mathlib.Data.Setoid.Basic

/-! # Envelope Dp -/

namespace OAI.AlgebraicGeometry.Crystalline.Cohomology.PD.EnvelopeDp.PDEnvelope

noncomputable section

/-!
# Cohomology: construction of relative divided-power envelopes

Ring expressions and ideal expressions are separate: divided powers are
only applied to expressions known to lie in the ideal. Expressions are
identified when their evaluations agree in every relative divided-power
algebra. The resulting quotient is small, even though its semantic
interpretation uses a product of all targets.
-/

universe u

variable (R A : Type u) [CommRing R] [CommRing A] [Algebra R A]
variable (I₀ : Ideal R) (δ₀ : DividedPowers I₀) (I : Ideal A)

/-- A target for the relative divided-power envelope, specified entirely
by ring-theoretic data. -/
structure Target where
  ring : CommRingCat.{u}
  [algebra : Algebra A ring]
  ideal : Ideal ring
  dp : DividedPowers ideal
  contains : I.map (algebraMap A ring) ≤ ideal
  baseDP : DividedPowers.IsDPMorphism δ₀ dp
    ((algebraMap A ring).comp (algebraMap R A))

attribute [instance] Target.algebra

mutual
  /-- Formal ring expressions with divided powers of ideal expressions. -/
  inductive RingTerm (A : Type u) [CommRing A] (I : Ideal A) where
    | coeff : A → RingTerm A I
    | add : RingTerm A I → RingTerm A I → RingTerm A I
    | neg : RingTerm A I → RingTerm A I
    | mul : RingTerm A I → RingTerm A I → RingTerm A I
    | ofIdeal : IdealTerm A I → RingTerm A I
  /-- Formal ideal expressions, closed under positive divided powers. -/
  inductive IdealTerm (A : Type u) [CommRing A] (I : Ideal A) where
    | seed : I → IdealTerm A I
    | zero : IdealTerm A I
    | add : IdealTerm A I → IdealTerm A I → IdealTerm A I
    | neg : IdealTerm A I → IdealTerm A I
    | smul : RingTerm A I → IdealTerm A I → IdealTerm A I
    | dp : ℕ → IdealTerm A I → IdealTerm A I
end

variable (T : Target R A I₀ δ₀ I)

mutual
  /-- Evaluate a ring expression in a relative divided-power target. -/
  def evalRing : RingTerm A I → T.ring
    | .coeff a => algebraMap A T.ring a
    | .add x y => evalRing x + evalRing y
    | .neg x => -evalRing x
    | .mul x y => evalRing x * evalRing y
    | .ofIdeal x => evalIdeal x
  /-- Evaluate an ideal expression in the target ideal. -/
  def evalIdeal : IdealTerm A I → T.ring
    | .seed x => algebraMap A T.ring x
    | .zero => 0
    | .add x y => evalIdeal x + evalIdeal y
    | .neg x => -evalIdeal x
    | .smul a x => evalRing a * evalIdeal x
    | .dp n x => T.dp.dpow (n + 1) (evalIdeal x)
end

/-- The ideal syntax evaluates inside the target ideal. -/
theorem evalIdeal_mem (t : IdealTerm A I) : evalIdeal R A I₀ δ₀ I T t ∈ T.ideal := by
  cases t with
  | seed x => exact T.contains (Ideal.mem_map_of_mem _ x.property)
  | zero => exact T.ideal.zero_mem
  | add x y => exact T.ideal.add_mem (evalIdeal_mem x) (evalIdeal_mem y)
  | neg x => exact T.ideal.neg_mem (evalIdeal_mem x)
  | smul a x => exact T.ideal.mul_mem_left _ (evalIdeal_mem x)
  | dp n x => exact T.dp.dpow_mem (Nat.succ_ne_zero n) (evalIdeal_mem x)
termination_by t

/-- All evaluations of a ring expression at once. -/
def semantics (t : RingTerm A I) : (T : Target R A I₀ δ₀ I) → T.ring :=
  fun T => evalRing R A I₀ δ₀ I T t

/-- The semantic image is closed under the ring operations. -/
def semanticRing : Subring ((T : Target R A I₀ δ₀ I) → T.ring) where
  carrier := Set.range (semantics R A I₀ δ₀ I)
  zero_mem' := ⟨.coeff 0, by funext T; exact map_zero (algebraMap A T.ring)⟩
  one_mem' := ⟨.coeff 1, by funext T; exact map_one (algebraMap A T.ring)⟩
  add_mem' := by rintro _ _ ⟨x, rfl⟩ ⟨y, rfl⟩; exact ⟨.add x y, rfl⟩
  neg_mem' := by rintro _ ⟨x, rfl⟩; exact ⟨.neg x, rfl⟩
  mul_mem' := by rintro _ _ ⟨x, rfl⟩ ⟨y, rfl⟩; exact ⟨.mul x y, rfl⟩

/-- A small quotient of formal expressions by equality in every target. -/
def Envelope : Type u := Quotient (Setoid.ker (semantics R A I₀ δ₀ I))

def semanticEquiv : Envelope R A I₀ δ₀ I ≃ semanticRing R A I₀ δ₀ I :=
  Setoid.quotientKerEquivRange (semantics R A I₀ δ₀ I)

instance envelopeCommRing : CommRing (Envelope R A I₀ δ₀ I) :=
  (semanticEquiv R A I₀ δ₀ I).commRing

def semanticRingEquiv : Envelope R A I₀ δ₀ I ≃+* semanticRing R A I₀ δ₀ I :=
  (semanticEquiv R A I₀ δ₀ I).ringEquiv

/-- The ring map evaluating the quotient in any target. -/
def evaluate : Envelope R A I₀ δ₀ I →+* T.ring :=
  (Pi.evalRingHom (fun T : Target R A I₀ δ₀ I => T.ring) T).comp
    ((semanticRing R A I₀ δ₀ I).subtype.comp (semanticRingEquiv R A I₀ δ₀ I).toRingHom)

def term (t : RingTerm A I) : Envelope R A I₀ δ₀ I := Quotient.mk _ t

@[simp]
theorem evaluate_term (t : RingTerm A I) :
    evaluate R A I₀ δ₀ I T (term R A I₀ δ₀ I t) = evalRing R A I₀ δ₀ I T t := rfl

/-- Equality in the envelope can be checked in every divided-power target. -/
theorem evaluate_ext {x y : Envelope R A I₀ δ₀ I}
    (h : ∀ T, evaluate R A I₀ δ₀ I T x = evaluate R A I₀ δ₀ I T y) : x = y := by
  apply (semanticRingEquiv R A I₀ δ₀ I).injective
  apply Subtype.ext
  exact funext h

/-- The canonical map from the original algebra to the envelope. -/
def ofAlgebra : A →+* Envelope R A I₀ δ₀ I where
  toFun a := term R A I₀ δ₀ I (.coeff a)
  map_one' := evaluate_ext R A I₀ δ₀ I (fun T => by simp [evalRing])
  map_mul' a b := evaluate_ext R A I₀ δ₀ I (fun T => by simp [evalRing])
  map_zero' := evaluate_ext R A I₀ δ₀ I (fun T => by simp [evalRing])
  map_add' a b := evaluate_ext R A I₀ δ₀ I (fun T => by simp [evalRing])

instance envelopeAlgebra : Algebra A (Envelope R A I₀ δ₀ I) :=
  (ofAlgebra R A I₀ δ₀ I).toAlgebra

@[simp]
theorem evaluate_ofAlgebra (a : A) :
    evaluate R A I₀ δ₀ I T (ofAlgebra R A I₀ δ₀ I a) = algebraMap A T.ring a := rfl

def idealTerm (t : IdealTerm A I) : Envelope R A I₀ δ₀ I :=
  term R A I₀ δ₀ I (.ofIdeal t)

@[simp]
theorem evaluate_idealTerm (t : IdealTerm A I) :
    evaluate R A I₀ δ₀ I T (idealTerm R A I₀ δ₀ I t) = evalIdeal R A I₀ δ₀ I T t := rfl

/-- The ideal generated by the original ideal and all positive divided powers. -/
def ideal : Ideal (Envelope R A I₀ δ₀ I) where
  carrier := Set.range (idealTerm R A I₀ δ₀ I)
  zero_mem' := ⟨.zero, evaluate_ext R A I₀ δ₀ I (fun T => by simp [evalIdeal])⟩
  add_mem' := by
    rintro _ _ ⟨x, rfl⟩ ⟨y, rfl⟩
    exact ⟨.add x y, evaluate_ext R A I₀ δ₀ I (fun T => by simp [evalIdeal])⟩
  smul_mem' := by
    intro a x hx
    obtain ⟨x, rfl⟩ := hx
    obtain ⟨a, rfl⟩ := Quotient.exists_rep a
    refine ⟨.smul a x, evaluate_ext R A I₀ δ₀ I (fun T => ?_)⟩
    change evalRing R A I₀ δ₀ I T a * evalIdeal R A I₀ δ₀ I T x =
      evaluate R A I₀ δ₀ I T (term R A I₀ δ₀ I a * idealTerm R A I₀ δ₀ I x)
    rw [map_mul, evaluate_term, evaluate_idealTerm]

theorem evaluate_mem {x : Envelope R A I₀ δ₀ I} (hx : x ∈ ideal R A I₀ δ₀ I) :
    evaluate R A I₀ δ₀ I T x ∈ T.ideal := by
  obtain ⟨t, rfl⟩ := hx
  exact evalIdeal_mem R A I₀ δ₀ I T t

def idealRep (x : Envelope R A I₀ δ₀ I) (hx : x ∈ ideal R A I₀ δ₀ I) : IdealTerm A I :=
  Classical.choose hx

theorem idealRep_spec (x : Envelope R A I₀ δ₀ I) (hx : x ∈ ideal R A I₀ δ₀ I) :
    idealTerm R A I₀ δ₀ I (idealRep R A I₀ δ₀ I x hx) = x :=
  Classical.choose_spec hx

open scoped Classical in
/-- Divided powers are applied to representatives in the ideal syntax. -/
def dpow (n : ℕ) (x : Envelope R A I₀ δ₀ I) : Envelope R A I₀ δ₀ I :=
  if hx : x ∈ ideal R A I₀ δ₀ I then
    match n with
    | 0 => 1
    | m + 1 => idealTerm R A I₀ δ₀ I (.dp m (idealRep R A I₀ δ₀ I x hx))
  else 0

theorem dpow_mem {n : ℕ} (hn : n ≠ 0) {x : Envelope R A I₀ δ₀ I}
    (hx : x ∈ ideal R A I₀ δ₀ I) : dpow R A I₀ δ₀ I n x ∈ ideal R A I₀ δ₀ I := by
  cases n with
  | zero => exact (hn rfl).elim
  | succ n =>
    rw [dpow, dite_eq_left hx]
    exact Set.mem_range_self _

/-- Evaluation respects divided powers on the envelope ideal. -/
theorem evaluate_dpow {x : Envelope R A I₀ δ₀ I} (hx : x ∈ ideal R A I₀ δ₀ I) (n : ℕ) :
    evaluate R A I₀ δ₀ I T (dpow R A I₀ δ₀ I n x) =
      T.dp.dpow n (evaluate R A I₀ δ₀ I T x) := by
  have ht := congrArg (evaluate R A I₀ δ₀ I T) (idealRep_spec R A I₀ δ₀ I x hx)
  change evalIdeal R A I₀ δ₀ I T (idealRep R A I₀ δ₀ I x hx) =
    evaluate R A I₀ δ₀ I T x at ht
  cases n with
  | zero => rw [dpow, dite_eq_left hx, map_one, T.dp.dpow_zero (evaluate_mem R A I₀ δ₀ I T hx)]
  | succ n => simp only [dpow, dite_eq_left hx, evaluate_idealTerm, evalIdeal, ht]

/-- The quotient carries an actual divided-power structure. -/
def dividedPowers : DividedPowers (ideal R A I₀ δ₀ I) where
  dpow := dpow R A I₀ δ₀ I
  dpow_null hx := dite_eq_right hx
  dpow_zero hx := by rw [dpow, dite_eq_left hx]
  dpow_one hx := evaluate_ext R A I₀ δ₀ I (fun T => by
    rw [evaluate_dpow R A I₀ δ₀ I T hx, T.dp.dpow_one (evaluate_mem R A I₀ δ₀ I T hx)])
  dpow_mem hn hx := dpow_mem R A I₀ δ₀ I hn hx
  dpow_add hx hy := evaluate_ext R A I₀ δ₀ I (fun T => by
    simp only [evaluate_dpow R A I₀ δ₀ I T ((ideal R A I₀ δ₀ I).add_mem hx hy),
      map_add, map_sum, map_mul, evaluate_dpow R A I₀ δ₀ I T hx, evaluate_dpow R A I₀ δ₀ I T hy]
    exact T.dp.dpow_add (evaluate_mem R A I₀ δ₀ I T hx) (evaluate_mem R A I₀ δ₀ I T hy))
  dpow_mul {n} a x hx := evaluate_ext R A I₀ δ₀ I (fun T => by
    simp only [evaluate_dpow R A I₀ δ₀ I T ((ideal R A I₀ δ₀ I).mul_mem_left a hx),
      map_mul, map_pow, evaluate_dpow R A I₀ δ₀ I T hx]
    exact T.dp.dpow_mul (evaluate_mem R A I₀ δ₀ I T hx))
  mul_dpow hx := evaluate_ext R A I₀ δ₀ I (fun T => by
    simp only [map_mul, map_natCast, evaluate_dpow R A I₀ δ₀ I T hx]
    exact T.dp.mul_dpow (evaluate_mem R A I₀ δ₀ I T hx))
  dpow_comp hn hx := evaluate_ext R A I₀ δ₀ I (fun T => by
    simp only [evaluate_dpow R A I₀ δ₀ I T (dpow_mem R A I₀ δ₀ I hn hx),
      evaluate_dpow R A I₀ δ₀ I T hx, map_mul, map_natCast]
    exact T.dp.dpow_comp hn (evaluate_mem R A I₀ δ₀ I T hx))

/-- The original ideal maps into the envelope ideal. -/
theorem contains : I.map (ofAlgebra R A I₀ δ₀ I) ≤ ideal R A I₀ δ₀ I := by
  rw [Ideal.map_le_iff_le_comap]
  intro x hx
  exact ⟨.seed ⟨x, hx⟩, evaluate_ext R A I₀ δ₀ I (fun _ => rfl)⟩

/-- Each evaluation is a divided-power morphism. -/
theorem evaluate_isDPMorphism :
    DividedPowers.IsDPMorphism (dividedPowers R A I₀ δ₀ I) T.dp (evaluate R A I₀ δ₀ I T) where
  ideal_comp := Ideal.map_le_iff_le_comap.mpr (fun _ hx => evaluate_mem R A I₀ δ₀ I T hx)
  dpow_comp _x hx := (evaluate_dpow R A I₀ δ₀ I T hx _).symm

variable (hbase : I₀.map (algebraMap R A) ≤ I)

include hbase in
/-- The envelope structure extends the specified divided powers of the base. -/
theorem base_isDPMorphism :
    DividedPowers.IsDPMorphism δ₀ (dividedPowers R A I₀ δ₀ I)
      ((ofAlgebra R A I₀ δ₀ I).comp (algebraMap R A)) where
  ideal_comp := by
    rw [Ideal.map_le_iff_le_comap]
    intro r hr
    exact contains R A I₀ δ₀ I (Ideal.mem_map_of_mem _
      (hbase (Ideal.mem_map_of_mem (algebraMap R A) hr)))
  dpow_comp r hr := by
    apply evaluate_ext R A I₀ δ₀ I
    intro T
    have hx : ofAlgebra R A I₀ δ₀ I (algebraMap R A r) ∈ ideal R A I₀ δ₀ I :=
      contains R A I₀ δ₀ I (Ideal.mem_map_of_mem _
        (hbase (Ideal.mem_map_of_mem (algebraMap R A) hr)))
    change evaluate R A I₀ δ₀ I T (dpow R A I₀ δ₀ I _
      (ofAlgebra R A I₀ δ₀ I (algebraMap R A r))) =
        evaluate R A I₀ δ₀ I T (ofAlgebra R A I₀ δ₀ I (algebraMap R A (δ₀.dpow _ r)))
    rw [evaluate_dpow R A I₀ δ₀ I T hx, evaluate_ofAlgebra, evaluate_ofAlgebra]
    exact T.baseDP.dpow_comp r hr

/-- The constructed envelope is itself a relative divided-power algebra. -/
def envelopeTarget : Target R A I₀ δ₀ I where
  ring := CommRingCat.of (Envelope R A I₀ δ₀ I)
  ideal := ideal R A I₀ δ₀ I
  dp := dividedPowers R A I₀ δ₀ I
  contains := contains R A I₀ δ₀ I
  baseDP := base_isDPMorphism R A I₀ δ₀ I hbase

@[simp]
theorem term_add (x y : RingTerm A I) :
    term R A I₀ δ₀ I (.add x y) = term R A I₀ δ₀ I x + term R A I₀ δ₀ I y :=
  evaluate_ext R A I₀ δ₀ I (fun T => by simp [evalRing])

@[simp]
theorem term_neg (x : RingTerm A I) : term R A I₀ δ₀ I (.neg x) = -term R A I₀ δ₀ I x :=
  evaluate_ext R A I₀ δ₀ I (fun T => by simp [evalRing])

@[simp]
theorem term_mul (x y : RingTerm A I) :
    term R A I₀ δ₀ I (.mul x y) = term R A I₀ δ₀ I x * term R A I₀ δ₀ I y :=
  evaluate_ext R A I₀ δ₀ I (fun T => by simp [evalRing])

@[simp]
theorem idealTerm_seed (x : I) : idealTerm R A I₀ δ₀ I (.seed x) = ofAlgebra R A I₀ δ₀ I x :=
  evaluate_ext R A I₀ δ₀ I (fun _ => rfl)

@[simp]
theorem idealTerm_zero : idealTerm R A I₀ δ₀ I .zero = 0 :=
  evaluate_ext R A I₀ δ₀ I (fun T => by simp [evalIdeal])

@[simp]
theorem idealTerm_add (x y : IdealTerm A I) :
    idealTerm R A I₀ δ₀ I (.add x y) = idealTerm R A I₀ δ₀ I x + idealTerm R A I₀ δ₀ I y :=
  evaluate_ext R A I₀ δ₀ I (fun T => by simp [evalIdeal])

@[simp]
theorem idealTerm_neg (x : IdealTerm A I) : idealTerm R A I₀ δ₀ I (.neg x) = -idealTerm R A I₀ δ₀ I x :=
  evaluate_ext R A I₀ δ₀ I (fun T => by simp [evalIdeal])

@[simp]
theorem idealTerm_smul (a : RingTerm A I) (x : IdealTerm A I) :
    idealTerm R A I₀ δ₀ I (.smul a x) = term R A I₀ δ₀ I a * idealTerm R A I₀ δ₀ I x :=
  evaluate_ext R A I₀ δ₀ I (fun T => by simp [evalIdeal])

theorem idealTerm_dp (n : ℕ) (x : IdealTerm A I) :
    idealTerm R A I₀ δ₀ I (.dp n x) =
      (dividedPowers R A I₀ δ₀ I).dpow (n + 1) (idealTerm R A I₀ δ₀ I x) := by
  apply evaluate_ext R A I₀ δ₀ I
  intro T
  change evalIdeal R A I₀ δ₀ I T (.dp n x) =
    evaluate R A I₀ δ₀ I T (dpow R A I₀ δ₀ I (n + 1) (idealTerm R A I₀ δ₀ I x))
  rw [evaluate_dpow R A I₀ δ₀ I T (Set.mem_range_self x), evaluate_idealTerm]
  rfl

/-- The canonical lift into a specified target, as an algebra map. -/
def lift : Envelope R A I₀ δ₀ I →ₐ[A] T.ring :=
  { evaluate R A I₀ δ₀ I T with
    commutes' := evaluate_ofAlgebra R A I₀ δ₀ I T }

variable (f : Envelope R A I₀ δ₀ I →ₐ[A] T.ring)

mutual
  /-- Any divided-power algebra map agrees with evaluation on ring expressions. -/
  theorem map_term (hf : DividedPowers.IsDPMorphism (dividedPowers R A I₀ δ₀ I) T.dp f.toRingHom)
      (t : RingTerm A I) : f (term R A I₀ δ₀ I t) = evalRing R A I₀ δ₀ I T t := by
    cases t with
    | coeff a => exact f.commutes a
    | add x y => rw [term_add, map_add, map_term hf x, map_term hf y]; rfl
    | neg x => rw [term_neg, map_neg, map_term hf x]; rfl
    | mul x y => rw [term_mul, map_mul, map_term hf x, map_term hf y]; rfl
    | ofIdeal x => exact map_idealTerm hf x
  termination_by sizeOf t
  /-- Any divided-power algebra map agrees with evaluation on ideal expressions. -/
  theorem map_idealTerm (hf : DividedPowers.IsDPMorphism (dividedPowers R A I₀ δ₀ I) T.dp f.toRingHom)
      (t : IdealTerm A I) :
      f (idealTerm R A I₀ δ₀ I t) = evalIdeal R A I₀ δ₀ I T t := by
    cases t with
    | seed x => rw [idealTerm_seed]; exact f.commutes x
    | zero => rw [idealTerm_zero, map_zero]; rfl
    | add x y => rw [idealTerm_add, map_add, map_idealTerm hf x, map_idealTerm hf y]; rfl
    | neg x => rw [idealTerm_neg, map_neg, map_idealTerm hf x]; rfl
    | smul a x => rw [idealTerm_smul, map_mul, map_term hf a, map_idealTerm hf x]; rfl
    | dp n x =>
      have hd : f ((dividedPowers R A I₀ δ₀ I).dpow (n + 1) (idealTerm R A I₀ δ₀ I x)) =
          T.dp.dpow (n + 1) (f (idealTerm R A I₀ δ₀ I x)) :=
        hf.map_dpow (Set.mem_range_self x)
      rw [idealTerm_dp, hd, map_idealTerm hf x]
      rfl
  termination_by sizeOf t
end

/-- The uniqueness part of the relative divided-power envelope's universal property. -/
theorem lift_unique
    (hf : DividedPowers.IsDPMorphism (dividedPowers R A I₀ δ₀ I) T.dp f.toRingHom) :
    f = lift R A I₀ δ₀ I T := by
  apply AlgHom.ext
  intro x
  obtain ⟨t, rfl⟩ := Quotient.exists_rep x
  exact map_term R A I₀ δ₀ I T f hf t

/-- The full universal mapping property, with existence and uniqueness proved. -/
theorem existsUnique_lift :
    ∃! g : Envelope R A I₀ δ₀ I →ₐ[A] T.ring,
      DividedPowers.IsDPMorphism (dividedPowers R A I₀ δ₀ I) T.dp g.toRingHom := by
  refine ⟨lift R A I₀ δ₀ I T, evaluate_isDPMorphism R A I₀ δ₀ I T, ?_⟩
  intro g hg
  exact lift_unique R A I₀ δ₀ I T g hg

variable {C : Type*} [CommRing C]
variable (g₁ g₂ : Envelope R A I₀ δ₀ I →+* C)
variable (hc : ∀ a, g₁ (ofAlgebra R A I₀ δ₀ I a) = g₂ (ofAlgebra R A I₀ δ₀ I a))
variable (hi : ∀ t, g₁ (idealTerm R A I₀ δ₀ I t) = g₂ (idealTerm R A I₀ δ₀ I t))

include hc hi in
theorem ringMaps_term (t : RingTerm A I) :
    g₁ (term R A I₀ δ₀ I t) = g₂ (term R A I₀ δ₀ I t) := by
  cases t with
  | coeff a => exact hc a
  | add x y => rw [term_add, map_add, map_add, ringMaps_term x, ringMaps_term y]
  | neg x => rw [term_neg, map_neg, map_neg, ringMaps_term x]
  | mul x y => rw [term_mul, map_mul, map_mul, ringMaps_term x, ringMaps_term y]
  | ofIdeal t => exact hi t
termination_by sizeOf t

include hc hi in
/-- Ring maps from the envelope are determined by coefficients and ideal expressions. -/
theorem ringHom_ext : g₁ = g₂ := by
  apply RingHom.ext
  intro x
  obtain ⟨t, rfl⟩ := Quotient.exists_rep x
  exact ringMaps_term R A I₀ δ₀ I g₁ g₂ hc hi t

end

end OAI.AlgebraicGeometry.Crystalline.Cohomology.PD.EnvelopeDp.PDEnvelope

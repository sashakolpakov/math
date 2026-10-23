import StickKnots.DoublyAlternating
import StickKnots.StrongLower
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Logic.Equiv.Set

/-!
# Typed certification layer for the long-word lower bound

This file replaces the free numerical populations in `StrongLower.lean` by
finite types and actual maps.  The alphabet is the already formalized type of
doubly down--up permutations, and a word is literally a `q`-tuple in that
alphabet.

The genuinely external braid and knot theory is isolated in two structures:

* `GarsideStageCertificate` supplies the braid normal-form interpretation,
  endpoint permutation, and the endpoint-correcting map to short pure braids;
* `KnotTransferCertificate` supplies the Malyutin--Stupakov injection, its arc
  bound, the Huh--Oh stick bound, and the structural description of forgetting
  orientation.  Lean derives the size-two fiber bound from that description.

Once those fields are supplied, all fiber counts and the final cardinal
inequality are proved below.  In particular, there are no free variables for
"the number of words", "the number of pure braids", or "the number of knots".
-/

namespace StickKnots

open Function

/-- Actual `q`-letter words in the doubly down--up alphabet on `4*k` strands. -/
abbrev GarsideWords (k q : ℕ) := Fin q → DoublyDownUpPerm (4 * k)

theorem card_garsideWords (k q : ℕ) :
    Fintype.card (GarsideWords k q) =
      Fintype.card (DoublyDownUpPerm (4 * k)) ^ q := by
  rw [Fintype.card_pi_const]

/-- Purity expressed in the only way needed by the counting argument: the
endpoint permutation is the identity. -/
def PureBraidFor {n : ℕ} {Braid : Type}
    (endpoint : Braid → Equiv.Perm (Fin n)) :=
  {b : Braid // endpoint b = 1}

/-- Data and external theorems needed for the Garside stage.

`normalForm_injective` is the uniqueness of the indicated left normal forms.
For a word with endpoint `u`, `purify u` models appending the fixed simple
factor with endpoint `u⁻¹`; its injectivity is right cancellation, and
`purify_factorLength` is the `q+1` positive-factor bound. -/
structure GarsideStageCertificate (k q : ℕ) where
  Braid : Type
  normalForm : GarsideWords k q → Braid
  normalForm_injective : Injective normalForm
  endpoint : Braid → Equiv.Perm (Fin (4 * k))
  appendSimple : Braid → Equiv.Perm (Fin (4 * k)) → Braid
  endpoint_appendSimple : ∀ b u,
    endpoint (appendSimple b u) = endpoint b * u
  appendSimple_injective : ∀ u, Injective (fun b ↦ appendSimple b u)
  factorLength : Braid → ℕ
  normalForm_factorLength : ∀ w, factorLength (normalForm w) ≤ q
  appendSimple_factorLength : ∀ b u,
    factorLength (appendSimple b u) ≤ factorLength b + 1

namespace GarsideStageCertificate

variable {k q : ℕ} (c : GarsideStageCertificate k q)

/-- Pure braids in the certified braid type, defined by trivial endpoint. -/
abbrev PureBraid : Type := PureBraidFor c.endpoint

/-- Endpoint permutation of a typed Garside word. -/
def wordEndpoint (w : GarsideWords k q) : Equiv.Perm (Fin (4 * k)) :=
  c.endpoint (c.normalForm w)

/-- The image of the word language in the certified braid type. -/
abbrev NormalFormFamily : Type := Set.range c.normalForm

noncomputable instance normalFormFamilyFintype : Fintype c.NormalFormFamily :=
  Fintype.ofEquiv (GarsideWords k q)
    (Equiv.ofInjective c.normalForm c.normalForm_injective)

/-- Garside uniqueness makes the normal-form encoding lose no words. -/
theorem card_normalFormFamily :
    Fintype.card c.NormalFormFamily = Fintype.card (GarsideWords k q) := by
  exact (Fintype.card_congr
    (Equiv.ofInjective c.normalForm c.normalForm_injective)).symm

/-- The actual finite fiber of words having endpoint permutation `u`. -/
abbrev EndpointFiber (u : Equiv.Perm (Fin (4 * k))) :=
  {w : GarsideWords k q // c.wordEndpoint w = u}

/-- Append the simple braid with inverse endpoint.  Lean checks from the
endpoint multiplication law that the result is pure. -/
def purify (u : Equiv.Perm (Fin (4 * k)))
    (w : c.EndpointFiber u) : c.PureBraid :=
  ⟨c.appendSimple (c.normalForm w.1) u⁻¹, by
    rw [c.endpoint_appendSimple]
    change c.wordEndpoint w.1 * u⁻¹ = 1
    rw [w.2]
    exact mul_inv_cancel u⟩

@[simp]
theorem purify_endpoint (u : Equiv.Perm (Fin (4 * k))) (w : c.EndpointFiber u) :
    c.endpoint (c.purify u w).1 = 1 :=
  (c.purify u w).2

/-- Right cancellation and normal-form uniqueness prove that endpoint
correction preserves distinctness. -/
theorem purify_injective (u : Equiv.Perm (Fin (4 * k))) :
    Injective (c.purify u) := by
  intro x y hxy
  apply Subtype.ext
  apply c.normalForm_injective
  apply c.appendSimple_injective u⁻¹
  exact congrArg Subtype.val hxy

/-- Appending one simple factor turns a `q`-factor normal form into a pure
braid of factor length at most `q+1`. -/
theorem purify_factorLength (u : Equiv.Perm (Fin (4 * k)))
    (w : c.EndpointFiber u) : c.factorLength (c.purify u w).1 ≤ q + 1 := by
  calc
    c.factorLength (c.purify u w).1 ≤
        c.factorLength (c.normalForm w.1) + 1 :=
      c.appendSimple_factorLength (c.normalForm w.1) u⁻¹
    _ ≤ q + 1 := Nat.add_le_add_right (c.normalForm_factorLength w.1) 1

/-- The corresponding family of certified short pure braids. -/
abbrev PureWordFamily (u : Equiv.Perm (Fin (4 * k))) : Type :=
  Set.range (c.purify u)

noncomputable instance pureWordFamilyFintype
    (u : Equiv.Perm (Fin (4 * k))) : Fintype (c.PureWordFamily u) :=
  Fintype.ofEquiv (c.EndpointFiber u)
    (Equiv.ofInjective (c.purify u) (c.purify_injective u))

theorem card_pureWordFamily (u : Equiv.Perm (Fin (4 * k))) :
    Fintype.card (c.PureWordFamily u) = Fintype.card (c.EndpointFiber u) := by
  exact (Fintype.card_congr
    (Equiv.ofInjective (c.purify u) (c.purify_injective u))).symm

theorem card_endpointFiber_eq_filter (u : Equiv.Perm (Fin (4 * k))) :
    Fintype.card (c.EndpointFiber u) =
      (Finset.univ.filter fun w : GarsideWords k q ↦ c.wordEndpoint w = u).card := by
  classical
  exact Fintype.card_subtype _

/-- Exact pigeonhole count for the full typed word language. -/
theorem exists_large_endpointFiber_exact :
    ∃ u : Equiv.Perm (Fin (4 * k)),
      Fintype.card (GarsideWords k q) ≤
        (4 * k).factorial * Fintype.card (c.EndpointFiber u) := by
  obtain ⟨u, hu⟩ := exists_endpointPermutation_fiber c.wordEndpoint
  refine ⟨u, ?_⟩
  rw [c.card_endpointFiber_eq_filter]
  exact hu

/-- The conventional ceiling form of the largest-fiber estimate. -/
theorem exists_endpointFiber_ceil_lower :
    ∃ u : Equiv.Perm (Fin (4 * k)),
      Fintype.card (GarsideWords k q) ⌈/⌉ (4 * k).factorial ≤
        Fintype.card (c.EndpointFiber u) := by
  obtain ⟨u, hu⟩ := c.exists_large_endpointFiber_exact
  exact ⟨u, (ceilDiv_le_iff_le_mul (Nat.factorial_pos (4 * k))).2 hu⟩

/-- Exact full-language count after endpoint correction to pure braids. -/
theorem exists_large_pureWordFamily_exact :
    ∃ u : Equiv.Perm (Fin (4 * k)),
      Fintype.card (GarsideWords k q) ≤
        (4 * k).factorial * Fintype.card (c.PureWordFamily u) := by
  obtain ⟨u, hu⟩ := c.exists_large_endpointFiber_exact
  exact ⟨u, by simpa [c.card_pureWordFamily u] using hu⟩

/-- The largest-fiber/pure-word count with the endpoint loss proved inside
Lean.  The certificate contributes only the typed injection to pure braids;
the pigeonhole calculation itself is not an external field. -/
theorem exists_large_pureWordFamily :
    ∃ u : Equiv.Perm (Fin (4 * k)),
      (k.factorial ^ 4) ^ q ≤
        (4 * k).factorial * Fintype.card (c.PureWordFamily u) := by
  obtain ⟨u, hu⟩ := c.exists_large_pureWordFamily_exact
  refine ⟨u, ?_⟩
  calc
    (k.factorial ^ 4) ^ q ≤
        Fintype.card (DoublyDownUpPerm (4 * k)) ^ q := by
      gcongr
      exact factorial_fourth_power_le_card_doublyDownUp k
    _ = Fintype.card (GarsideWords k q) := by
      rw [card_garsideWords]
    _ ≤ (4 * k).factorial * Fintype.card (c.PureWordFamily u) := hu

/-- The same internally counted family, kept as its source fiber.  This form
is convenient for composing the certified maps below. -/
theorem exists_large_endpointFiber :
    ∃ u : Equiv.Perm (Fin (4 * k)),
      (k.factorial ^ 4) ^ q ≤
        (4 * k).factorial * Fintype.card (c.EndpointFiber u) := by
  obtain ⟨u, hu⟩ := c.exists_large_pureWordFamily
  exact ⟨u, by simpa [c.card_pureWordFamily u] using hu⟩

end GarsideStageCertificate

/-- Integer form of the Huh--Oh stick budget
`floor (3/2 * (arcIndex - 1))`. -/
def huhOhStickBudget (arcIndex : ℕ) : ℕ := 3 * (arcIndex - 1) / 2

theorem huhOhStickBudget_mono : Monotone huhOhStickBudget := by
  intro a b hab
  exact Nat.div_le_div_right (Nat.mul_le_mul_left 3 (Nat.sub_le_sub_right hab 1))

/-- Knot types lying within a specified stick budget. -/
def BoundedKnotTypes {KnotType : Type} (stickNumber : KnotType → ℕ) (N : ℕ) :=
  {K : KnotType // stickNumber K ≤ N}

/-- A property-restricted family, literally a subtype of the bounded knot
types.  The lower construction uses `P = isPrimeSatellite`. -/
def BoundedKnotTypesWith {KnotType : Type} (stickNumber : KnotType → ℕ)
    (N : ℕ) (P : KnotType → Prop) :=
  {K : BoundedKnotTypes stickNumber N // P K.1}

/-- Typed external inputs for the passage from short pure braids to bounded
ordinary knot types.

The ambient types of all oriented and unoriented knots need not be finite.
Only the bounded prime-satellite subtype is assumed finite, exactly where
finite cardinality is used; the orientation-fiber finiteness and cardinal
bound are derived below. -/
structure KnotTransferCertificate {k q : ℕ}
    (c : GarsideStageCertificate k q)
    (OrientedKnot KnotType : Type) where
  malyutinStupakov : c.PureBraid → OrientedKnot
  malyutinStupakov_injective : Injective malyutinStupakov
  arcIndex : OrientedKnot → ℕ
  malyutinStupakov_arc_bound : ∀ b : c.PureBraid,
    arcIndex (malyutinStupakov b) ≤
      (4 * k) * max 11 (c.factorLength b.1 + 8) - 4
  forgetOrientation : OrientedKnot → KnotType
  reverseOrientation : OrientedKnot → OrientedKnot
  reverseOrientation_involutive : Involutive reverseOrientation
  forgetOrientation_eq_iff : ∀ J J' : OrientedKnot,
    forgetOrientation J' = forgetOrientation J ↔
      J' = J ∨ J' = reverseOrientation J
  stickNumber : KnotType → ℕ
  isPrimeSatellite : KnotType → Prop
  isNontrivial : KnotType → Prop
  malyutinStupakov_primeSatellite : ∀ b : c.PureBraid,
    isPrimeSatellite (forgetOrientation (malyutinStupakov b))
  primeSatellite_nontrivial : ∀ K : KnotType,
    isPrimeSatellite K → isNontrivial K
  huhOh_stick_bound : ∀ J : OrientedKnot,
    isNontrivial (forgetOrientation J) →
      stickNumber (forgetOrientation J) ≤ huhOhStickBudget (arcIndex J)

namespace KnotTransferCertificate

variable {k q : ℕ} {c : GarsideStageCertificate k q}
variable {OrientedKnot KnotType : Type}
variable (t : KnotTransferCertificate c OrientedKnot KnotType)

abbrev longWordStickBudget (k q : ℕ) : ℕ :=
  huhOhStickBudget (wordArcBudget (4 * k) q)

abbrev BoundedKnots {k q : ℕ} {c : GarsideStageCertificate k q}
    {OrientedKnot KnotType : Type}
    (t : KnotTransferCertificate c OrientedKnot KnotType) : Type :=
  @BoundedKnotTypesWith KnotType t.stickNumber (longWordStickBudget k q)
    t.isPrimeSatellite

/-- The printed Malyutin--Stupakov estimate plus the Lean-verified `q+1`
factor-length bound gives exactly `wordArcBudget (4*k) q`. -/
theorem purified_arc_bound (u : Equiv.Perm (Fin (4 * k)))
    (w : c.EndpointFiber u) :
    t.arcIndex (t.malyutinStupakov (c.purify u w)) ≤ wordArcBudget (4 * k) q := by
  calc
    t.arcIndex (t.malyutinStupakov (c.purify u w)) ≤
        (4 * k) * max 11 (c.factorLength (c.purify u w).1 + 8) - 4 :=
      t.malyutinStupakov_arc_bound (c.purify u w)
    _ ≤ (4 * k) * max 11 (q + 9) - 4 := by
      apply Nat.sub_le_sub_right
      apply Nat.mul_le_mul_left
      apply max_le_max_left
      have hLength := c.purify_factorLength u w
      omega
    _ = wordArcBudget (4 * k) q := rfl

/-- Prime-satellite nontriviality and Huh--Oh turn the purified arc estimate
into the claimed stick estimate. -/
theorem purified_stick_bound (u : Equiv.Perm (Fin (4 * k)))
    (w : c.EndpointFiber u) :
    t.stickNumber
        (t.forgetOrientation (t.malyutinStupakov (c.purify u w))) ≤
      longWordStickBudget k q := by
  calc
    t.stickNumber
        (t.forgetOrientation (t.malyutinStupakov (c.purify u w))) ≤
        huhOhStickBudget
          (t.arcIndex (t.malyutinStupakov (c.purify u w))) :=
      t.huhOh_stick_bound _ <|
        t.primeSatellite_nontrivial _
          (t.malyutinStupakov_primeSatellite (c.purify u w))
    _ ≤ longWordStickBudget k q :=
      huhOhStickBudget_mono (purified_arc_bound t u w)

/-- The Malyutin--Stupakov map, forgetting orientation and using Huh--Oh, as
an actual map into the subtype of bounded prime satellite knots. -/
def boundedKnotMap (u : Equiv.Perm (Fin (4 * k))) :
    c.EndpointFiber u → BoundedKnots t := fun w ↦
  ⟨⟨t.forgetOrientation (t.malyutinStupakov (c.purify u w)),
      purified_stick_bound t u w⟩,
    t.malyutinStupakov_primeSatellite (c.purify u w)⟩

/-- A fiber of the bounded-knot map injects into the corresponding fiber of
forgetting orientation.  This is where the Malyutin--Stupakov and purification
injections are used. -/
def boundedFiberToOrientationFiber
    (u : Equiv.Perm (Fin (4 * k))) (K : BoundedKnots t) :
    {w : c.EndpointFiber u // boundedKnotMap t u w = K} →
      {J : OrientedKnot // t.forgetOrientation J = K.1.1} := fun w ↦
  ⟨t.malyutinStupakov (c.purify u w.1),
    congrArg (fun z : BoundedKnots t ↦ z.1.1) w.2⟩

theorem boundedFiberToOrientationFiber_injective
    (u : Equiv.Perm (Fin (4 * k))) (K : BoundedKnots t) :
    Injective (boundedFiberToOrientationFiber t u K) := by
  intro x y hxy
  apply Subtype.ext
  apply c.purify_injective u
  apply t.malyutinStupakov_injective
  exact congrArg Subtype.val hxy

/-- The structural description of forgetting orientation produces an
injection of every fiber into a two-element type. -/
theorem exists_forgetOrientation_fiber_injection (K : KnotType) :
    ∃ code : {J : OrientedKnot // t.forgetOrientation J = K} → Fin 2,
      Injective code := by
  classical
  by_cases hNonempty : Nonempty {J : OrientedKnot // t.forgetOrientation J = K}
  · let J₀ : {J : OrientedKnot // t.forgetOrientation J = K} :=
      Classical.choice hNonempty
    let code : {J : OrientedKnot // t.forgetOrientation J = K} → Fin 2 :=
      fun J ↦ if J.1 = J₀.1 then 0 else 1
    have classify (J : {J : OrientedKnot // t.forgetOrientation J = K}) :
        J.1 = J₀.1 ∨ J.1 = t.reverseOrientation J₀.1 := by
      apply (t.forgetOrientation_eq_iff J₀.1 J.1).mp
      exact J.2.trans J₀.2.symm
    have code_injective : Injective code := by
      intro J J' hCode
      apply Subtype.ext
      by_cases hJ : J.1 = J₀.1
      · have hJ' : J'.1 = J₀.1 := by
          by_contra hJ'
          simp [code, hJ, hJ'] at hCode
        exact hJ.trans hJ'.symm
      · have hJ' : ¬J'.1 = J₀.1 := by
          intro hJ'
          simp [code, hJ, hJ'] at hCode
        rcases classify J with hBase | hReverse
        · exact (hJ hBase).elim
        · rcases classify J' with hBase' | hReverse'
          · exact (hJ' hBase').elim
          · exact hReverse.trans hReverse'.symm
    exact ⟨code, code_injective⟩
  · refine ⟨fun J ↦ (hNonempty ⟨J⟩).elim, ?_⟩
    intro J
    exact (hNonempty ⟨J⟩).elim

/-- Every orientation-forgetting fiber is finite, derived rather than assumed. -/
theorem forgetOrientation_fiber_finite (K : KnotType) :
    Finite {J : OrientedKnot // t.forgetOrientation J = K} := by
  obtain ⟨code, hCode⟩ := exists_forgetOrientation_fiber_injection t K
  exact Finite.of_injective code hCode

/-- Forgetting orientation has fibers of size at most two.  Lean derives the
cardinal statement from the structural fact that an unoriented class consists
of an oriented class and possibly its reversal. -/
theorem forgetOrientation_fiber_le_two (K : KnotType) :
    Nat.card {J : OrientedKnot // t.forgetOrientation J = K} ≤ 2 := by
  letI : Finite {J : OrientedKnot // t.forgetOrientation J = K} :=
    forgetOrientation_fiber_finite t K
  obtain ⟨code, hCode⟩ := exists_forgetOrientation_fiber_injection t K
  calc
    Nat.card {J : OrientedKnot // t.forgetOrientation J = K} ≤ Nat.card (Fin 2) :=
      Nat.card_le_card_of_injective code hCode
    _ = 2 := by simp

/-- Every fiber of the composed map to ordinary bounded knots has size at
most two.  The proof derives this from the typed injections and the structural
orientation-reversal characterization. -/
theorem boundedKnotMap_fiber_le_two
    (u : Equiv.Perm (Fin (4 * k))) (K : BoundedKnots t) :
    Nat.card {w : c.EndpointFiber u // boundedKnotMap t u w = K} ≤ 2 := by
  letI : Finite {J : OrientedKnot // t.forgetOrientation J = K.1.1} :=
    forgetOrientation_fiber_finite t K.1.1
  calc
    Nat.card {w : c.EndpointFiber u // boundedKnotMap t u w = K} ≤
        Nat.card {J : OrientedKnot // t.forgetOrientation J = K.1.1} :=
      Nat.card_le_card_of_injective (boundedFiberToOrientationFiber t u K)
        (boundedFiberToOrientationFiber_injective t u K)
    _ ≤ 2 := forgetOrientation_fiber_le_two t K.1.1

/-- Finite cardinality is the sum of the cardinalities of the fibers; hence a
uniform fiber bound `r` costs at most a factor `r`. -/
theorem natCard_le_natCard_mul_of_fiber_le
    {α β : Type*} [Finite α] [Finite β]
    (f : α → β) (r : ℕ)
    (h : ∀ y, Nat.card {x : α // f x = y} ≤ r) :
    Nat.card α ≤ Nat.card β * r := by
  classical
  letI : Fintype α := Fintype.ofFinite α
  letI : Fintype β := Fintype.ofFinite β
  simp only [Nat.card_eq_fintype_card] at h ⊢
  calc
    Fintype.card α = Fintype.card (Σ y : β, {x : α // f x = y}) :=
      (Fintype.card_congr (Equiv.sigmaFiberEquiv f)).symm
    _ = ∑ y : β, Fintype.card {x : α // f x = y} := Fintype.card_sigma
    _ ≤ ∑ _y : β, r := Finset.sum_le_sum fun y _ ↦ h y
    _ = Fintype.card β * r := by simp

/-- All short pure words in a fixed endpoint fiber yield at least half as many
ordinary bounded prime satellite knot types. -/
theorem endpointFiber_card_le_twice_boundedKnots
    [Finite (BoundedKnots t)] (u : Equiv.Perm (Fin (4 * k))) :
    Fintype.card (c.EndpointFiber u) ≤ 2 * Nat.card (BoundedKnots t) := by
  classical
  letI : Fintype (BoundedKnots t) := Fintype.ofFinite _
  have h := natCard_le_natCard_mul_of_fiber_le (boundedKnotMap t u) 2
    (boundedKnotMap_fiber_le_two t u)
  simpa [Nat.card_eq_fintype_card, Nat.mul_comm] using h

/-- Fully typed finite lower-bound transfer for the complete doubly down--up
alphabet.  This is the exact Lean counterpart of the `g_n^q` count in the
manuscript, specialized to `n = 4*k`. -/
theorem finite_stick_lower_bound_full_language [Finite (BoundedKnots t)] :
    Fintype.card (DoublyDownUpPerm (4 * k)) ^ q ≤
      2 * (4 * k).factorial * Nat.card (BoundedKnots t) := by
  obtain ⟨u, hu⟩ := GarsideStageCertificate.exists_large_endpointFiber_exact c
  calc
    Fintype.card (DoublyDownUpPerm (4 * k)) ^ q =
        Fintype.card (GarsideWords k q) := by rw [card_garsideWords]
    _ ≤
        (4 * k).factorial * Fintype.card (c.EndpointFiber u) := hu
    _ ≤ (4 * k).factorial * (2 * Nat.card (BoundedKnots t)) :=
      Nat.mul_le_mul_left _ (endpointFiber_card_le_twice_boundedKnots t u)
    _ = 2 * (4 * k).factorial * Nat.card (BoundedKnots t) := by ring

/-- Explicit factorial-scale corollary using the formalized quarter-family.
The endpoint, pure-braid, and bounded prime-satellite knot populations are all
cardinalities of actual types; no numerical population is a free variable. -/
theorem finite_stick_lower_bound [Finite (BoundedKnots t)] :
    (k.factorial ^ 4) ^ q ≤
      2 * (4 * k).factorial * Nat.card (BoundedKnots t) := by
  calc
    (k.factorial ^ 4) ^ q ≤
        Fintype.card (DoublyDownUpPerm (4 * k)) ^ q := by
      gcongr
      exact factorial_fourth_power_le_card_doublyDownUp k
    _ ≤ 2 * (4 * k).factorial * Nat.card (BoundedKnots t) :=
      finite_stick_lower_bound_full_language t

end KnotTransferCertificate

end StickKnots

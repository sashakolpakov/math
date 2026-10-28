import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Ordinary.TorsionCounts

/-! # Torsion Coordinate Maps -/

namespace OAI

noncomputable section

namespace AlgebraicGeometry.HodgeConjecture.HeckeCycles.TorsionCoordinateMaps.CM.Primary

/-! To identify a bounded prime-power torsion group, it suffices to
detect the kernel on its prime-torsion subgroup. This will allow lifted
ordinary torsion coordinates to be checked at their first level. -/

variable {A B : Type*} [Group A] [Group B]

theorem kernel_trivial_of_prime_torsion (q : ℕ) (f : A →* B)
    (htor : ∀ a : A, a ^ q = 1 → f a = 1 → a = 1)
    (n : ℕ) (a : A) (hkill : a ^ (q ^ n) = 1) (ha : f a = 1) : a = 1 := by
  induction n generalizing a with
  | zero => simpa only [pow_zero, pow_one] using hkill
  | succ n ih =>
    apply htor a
    · apply ih (a ^ q)
      · simpa only [← pow_mul, ← pow_succ'] using hkill
      · rw [map_pow, ha, one_pow]
    · exact ha

theorem injective_of_prime_torsion (q n : ℕ) (f : A →* B)
    (hkill : ∀ a : A, a ^ (q ^ n) = 1)
    (htor : ∀ a : A, a ^ q = 1 → f a = 1 → a = 1) :
    Function.Injective f := by
  apply (MonoidHom.ker_eq_bot_iff f).mp
  apply le_antisymm _ bot_le
  intro a ha
  exact (Subgroup.mem_bot).mpr
    (kernel_trivial_of_prime_torsion q f htor n a (hkill a) ha)

end AlgebraicGeometry.HodgeConjecture.HeckeCycles.TorsionCoordinateMaps.CM.Primary

namespace AlgebraicGeometry.HodgeConjecture.HeckeCycles.TorsionCoordinateMaps.CM.Criterion

/-! A proposed set of lifted ordinary coordinates gives the full
q-power torsion group once its first-level kernel is detected. The
surjectivity follows from the proved geometric torsion count. -/

abbrev coordinates (q n g : ℕ) := Multiplicative (Fin g → ZMod (q ^ n))

instance (q n g : ℕ) : CommGroup (coordinates q n g) :=
  inferInstanceAs (CommGroup (Multiplicative (Fin g → ZMod (q ^ n))))

theorem coordinates_killed (q n g : ℕ) (x : coordinates q n g) : x ^ (q ^ n) = 1 := by
  apply Multiplicative.toAdd.injective
  change (q ^ n) • x.toAdd = 0
  ext i
  change (q ^ n) • x.toAdd i = 0
  simp only [nsmul_eq_mul, ZMod.natCast_self, zero_mul]

theorem coordinates_card (q n g : ℕ) (hq : q ≠ 0) :
    Nat.card (coordinates q n g) = q ^ (n * g) := by
  let : NeZero (q ^ n) := ⟨pow_ne_zero n hq⟩
  change Nat.card (Multiplicative (Fin g → ZMod (q ^ n))) = _
  simp only [Nat.card_eq_fintype_card, Fintype.card_multiplicative,
    Fintype.card_fun, Fintype.card_fin, ZMod.card, ← pow_mul]

def coordinateEquiv {A : Type*} [Group A] (q n g : ℕ) (hq : q ≠ 0)
    (hcard : Nat.card A = q ^ (n * g))
    (f : coordinates q n g →* A)
    (htor : ∀ x : coordinates q n g, x ^ q = 1 → f x = 1 → x = 1) :
    coordinates q n g ≃* A := by
  let : Finite A := Nat.finite_of_card_ne_zero (hcard ▸ pow_ne_zero (n * g) hq)
  have hi := Primary.injective_of_prime_torsion q n f
    (coordinates_killed q n g) htor
  exact MulEquiv.ofBijective f ((Nat.bijective_iff_injective_and_card f).mpr
    ⟨hi, (coordinates_card q n g hq).trans hcard.symm⟩)

end AlgebraicGeometry.HodgeConjecture.HeckeCycles.TorsionCoordinateMaps.CM.Criterion

namespace AlgebraicGeometry.HodgeConjecture.HeckeCycles.TorsionCoordinateMaps.CM

/-! Construct the actual coordinate homomorphism from chosen torsion
generators. The only relation required of each generator is its original
power-torsion equation. -/

variable {A : Type*} [CommGroup A]

def cyclicMap (m : ℕ) (a : A) (ha : a ^ m = 1) : Multiplicative (ZMod m) →* A := by
  let f : ℤ →+ Additive A := zmultiplesHom (Additive A) (Additive.ofMul a)
  have hf : f m = 0 := by
    change (m : ℤ) • Additive.ofMul a = 0
    rw [natCast_zsmul]
    exact congrArg Additive.ofMul ha
  let z := ZMod.lift m ⟨f, hf⟩
  exact
    { toFun := fun x => (z x.toAdd).toMul
      map_one' := congrArg Additive.toMul z.map_zero
      map_mul' := fun x y => congrArg Additive.toMul (z.map_add x.toAdd y.toAdd) }

theorem cyclicMap_generator (m : ℕ) (a : A) (ha : a ^ m = 1) :
    cyclicMap m a ha (Multiplicative.ofAdd (1 : ZMod m)) = a := by
  change Additive.toMul (ZMod.lift (A := Additive A) m _ (1 : ZMod m)) = a
  rw [show (1 : ZMod m) = ((1 : ℤ) : ZMod m) from (Int.cast_one).symm, ZMod.lift_coe]
  change ((1 : ℤ) • Additive.ofMul a).toMul = a
  rw [one_zsmul]
  rfl

open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.TorsionCoordinateMaps.CM.Criterion

def coordinateMap (q n g : ℕ) (a : Fin g → A) (ha : ∀ i, a i ^ (q ^ n) = 1) :
    Criterion.coordinates q n g →* A where
  toFun x := ∏ i, cyclicMap (q ^ n) (a i) (ha i) (Multiplicative.ofAdd (x.toAdd i))
  map_one' := by
    change (∏ i, cyclicMap (q ^ n) (a i) (ha i) 1) = 1
    simp only [map_one, Finset.prod_const_one]
  map_mul' x y := by
    change (∏ i, cyclicMap (q ^ n) (a i) (ha i)
      (Multiplicative.ofAdd (x.toAdd i) * Multiplicative.ofAdd (y.toAdd i))) = _
    simp only [map_mul, Finset.prod_mul_distrib]

theorem coordinateMap_generator (q n g : ℕ) (a : Fin g → A)
    (ha : ∀ i, a i ^ (q ^ n) = 1) (i : Fin g) :
    coordinateMap q n g a ha (Multiplicative.ofAdd (Pi.single i (1 : ZMod (q ^ n)))) = a i := by
  classical
  change (∏ j, cyclicMap (q ^ n) (a j) (ha j)
    (Multiplicative.ofAdd ((Pi.single i (1 : ZMod (q ^ n)) : Fin g → ZMod (q ^ n)) j))) = a i
  rw [Finset.prod_eq_single i]
  · simpa only [Pi.single_eq_same] using cyclicMap_generator (q ^ n) (a i) (ha i)
  · intro j _ hji
    rw [Pi.single_eq_of_ne hji]
    exact map_one _
  · simp

end AlgebraicGeometry.HodgeConjecture.HeckeCycles.TorsionCoordinateMaps.CM

namespace AlgebraicGeometry.HodgeConjecture.HeckeCycles.TorsionCoordinateMaps.CM.FirstLevel

/-! Division lifts first-level geometric torsion generators to every
power level. The resulting coordinate map is constructed explicitly. -/

variable {A : Type*} [CommGroup A]

def firstLevel (q n : ℕ) : AbelianScheme.FrobeniusKernel.OrdinaryIsogeny.Construction.qTorsion A (q ^ (n + 1)) →* AbelianScheme.FrobeniusKernel.OrdinaryIsogeny.Construction.qTorsion A q where
  toFun x := ⟨x.val ^ (q ^ n), by
    change (x.val ^ (q ^ n)) ^ q = 1
    rw [← pow_mul, ← pow_succ]
    exact x.property⟩
  map_one' := Subtype.ext (one_pow (q ^ n))
  map_mul' x y := Subtype.ext (mul_pow x.val y.val (q ^ n))

theorem power_division (q : ℕ) (hdiv : Function.Surjective (fun a : A => a ^ q))
    (n : ℕ) : Function.Surjective (fun a : A => a ^ (q ^ n)) := by
  induction n with
  | zero =>
    intro a
    exact ⟨a, by simp only [pow_zero, pow_one]⟩
  | succ n ih =>
    intro a
    obtain ⟨b, hb⟩ := hdiv a
    obtain ⟨c, hc⟩ := ih b
    have hb' : b ^ q = a := hb
    have hc' : c ^ (q ^ n) = b := hc
    refine ⟨c, ?_⟩
    change c ^ (q ^ (n + 1)) = a
    rw [pow_succ, pow_mul, hc', hb']

theorem firstLevel_surjective (q n : ℕ)
    (hdiv : Function.Surjective (fun a : A => a ^ q)) :
    Function.Surjective (firstLevel (A := A) q n) := by
  intro x
  obtain ⟨a, ha⟩ := power_division q hdiv n x.val
  have ha' : a ^ (q ^ n) = x.val := ha
  have hk : a ^ (q ^ (n + 1)) = 1 := by
    rw [pow_succ, pow_mul, ha']
    exact x.property
  exact ⟨⟨a, hk⟩, Subtype.ext ha'⟩

open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.TorsionCoordinateMaps.CM.Criterion OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.TorsionCoordinateMaps.CM

theorem exists_lifted_coordinateMap (q n g : ℕ)
    (hdiv : Function.Surjective (fun a : A => a ^ q))
    (a : Fin g → AbelianScheme.FrobeniusKernel.OrdinaryIsogeny.Construction.qTorsion A q) :
    ∃ f : Criterion.coordinates q (n + 1) g →* AbelianScheme.FrobeniusKernel.OrdinaryIsogeny.Construction.qTorsion A (q ^ (n + 1)),
      ∀ i : Fin g,
        firstLevel q n (f (Multiplicative.ofAdd (Pi.single i (1 : ZMod (q ^ (n + 1)))))) = a i := by
  classical
  choose b hb using fun i => firstLevel_surjective q n hdiv (a i)
  have hkill (i : Fin g) : b i ^ (q ^ (n + 1)) = 1 :=
    Subtype.ext (b i).property
  refine ⟨coordinateMap q (n + 1) g b hkill, fun i => ?_⟩
  exact (congrArg (firstLevel q n)
    (coordinateMap_generator q (n + 1) g b hkill i)).trans (hb i)

end AlgebraicGeometry.HodgeConjecture.HeckeCycles.TorsionCoordinateMaps.CM.FirstLevel

end

end OAI

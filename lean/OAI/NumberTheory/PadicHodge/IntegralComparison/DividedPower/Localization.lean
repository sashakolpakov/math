import Mathlib

/-! # Localization -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.DividedPower.Localization

noncomputable section

/-!
# IntegralComparison: divided powers on localizations

The construction uses the forced formula γₙ(x/s) = γₙ(x)/sⁿ for x in
the divided-power ideal. Well-definedness allows zero divisors and
localizations in which some elements vanish.
-/

open _root_.Ideal

universe u v

variable {A : Type u} [CommRing A] {I : Ideal A} (δ : DividedPowers I)
variable (M : Submonoid A) (S : Type v) [CommRing S] [Algebra A S] [IsLocalization M S]

lemma fraction_dpow_congr {x y : A} (hx : x ∈ I) (hy : y ∈ I) (s t : M)
    (h : IsLocalization.mk' S x s = IsLocalization.mk' S y t) (n : ℕ) :
    IsLocalization.mk' S (δ.dpow n x) (s ^ n) =
      IsLocalization.mk' S (δ.dpow n y) (t ^ n) := by
  obtain ⟨c, hc⟩ := (IsLocalization.eq (M := M) (S := S)).mp h
  apply (IsLocalization.eq (M := M) (S := S)).mpr
  refine ⟨c ^ n, ?_⟩
  have he := congrArg (δ.dpow n) hc
  simpa only [δ.dpow_mul (I.mul_mem_left _ hx), δ.dpow_mul (I.mul_mem_left _ hy),
    δ.dpow_mul hx, δ.dpow_mul hy, SubmonoidClass.coe_pow] using he

lemma ideal_fraction {z : S} (hz : z ∈ I.map (algebraMap A S)) :
    ∃ (x : I) (s : M), IsLocalization.mk' S (x : A) s = z := by
  obtain ⟨⟨x, s⟩, h⟩ := (IsLocalization.mem_map_algebraMap_iff M S).mp hz
  exact ⟨x, s, (IsLocalization.eq_mk'_iff_mul_eq.mpr h).symm⟩

def numerator (z : S) (hz : z ∈ I.map (algebraMap A S)) : I :=
  (ideal_fraction M S hz).choose

def denominator (z : S) (hz : z ∈ I.map (algebraMap A S)) : M :=
  (ideal_fraction M S hz).choose_spec.choose

lemma fraction_spec (z : S) (hz : z ∈ I.map (algebraMap A S)) :
    IsLocalization.mk' S (numerator M S z hz : A) (denominator M S z hz) = z :=
  (ideal_fraction M S hz).choose_spec.choose_spec

def dpow (n : ℕ) (z : S) : S := by
  classical
  exact if hz : z ∈ I.map (algebraMap A S) then
    IsLocalization.mk' S (δ.dpow n (numerator M S z hz)) (denominator M S z hz ^ n)
  else 0

lemma fraction_mem (x : A) (hx : x ∈ I) (s : M) :
    IsLocalization.mk' S x s ∈ I.map (algebraMap A S) :=
  IsLocalization.mk'_mem_iff.mpr (Ideal.mem_map_of_mem _ hx)

lemma dpow_fraction (n : ℕ) {x : A} (hx : x ∈ I) (s : M) :
    Localization.dpow δ M S n (IsLocalization.mk' S x s) =
      IsLocalization.mk' S (δ.dpow n x) (s ^ n) := by
  classical
  rw [Localization.dpow, dite_eq_left (fraction_mem M S x hx s)]
  exact fraction_dpow_congr δ M S (numerator M S _ _).property hx _ s
    (fraction_spec M S _ _) n

lemma dpow_algebraMap (n : ℕ) {x : A} (hx : x ∈ I) :
    Localization.dpow δ M S n (algebraMap A S x) = algebraMap A S (δ.dpow n x) := by
  rw [← IsLocalization.mk'_one (M := M) S x, dpow_fraction δ M S n hx,
    one_pow, IsLocalization.mk'_one]

lemma fraction_sum {ι : Type*} (t : Finset ι) (x : ι → A) (s : M) :
    IsLocalization.mk' S (∑ i ∈ t, x i) s = ∑ i ∈ t, IsLocalization.mk' S (x i) s := by
  rw [IsLocalization.mk'_eq_mul_mk'_one, map_sum, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro i hi
  exact (IsLocalization.mk'_eq_mul_mk'_one (S := S) (x i) s).symm

lemma fraction_add_same (x y : A) (s : M) :
    IsLocalization.mk' S (x + y) s = IsLocalization.mk' S x s + IsLocalization.mk' S y s := by
  rw [IsLocalization.mk'_eq_mul_mk'_one (S := S) (x + y) s, map_add, add_mul,
    IsLocalization.mk'_eq_mul_mk'_one (S := S) x s, IsLocalization.mk'_eq_mul_mk'_one (S := S) y s]

lemma fraction_common (x : A) (s t : M) :
    IsLocalization.mk' S ((t : A) * x) (t * s) = IsLocalization.mk' S x s := by
  rw [IsLocalization.mk'_mul, IsLocalization.mk'_self, one_mul]

lemma ideal_pair_fraction {x y : S} (hx : x ∈ I.map (algebraMap A S))
    (hy : y ∈ I.map (algebraMap A S)) :
    ∃ (a b : I) (s : M), IsLocalization.mk' S (a : A) s = x ∧
      IsLocalization.mk' S (b : A) s = y := by
  obtain ⟨a, s, rfl⟩ := ideal_fraction M S hx
  obtain ⟨b, t, rfl⟩ := ideal_fraction M S hy
  refine ⟨⟨(t : A) * a, I.mul_mem_left _ a.property⟩,
    ⟨(s : A) * b, I.mul_mem_left _ b.property⟩, t * s,
    fraction_common M S _ _ _, ?_⟩
  rw [mul_comm t s]
  exact fraction_common M S _ _ _

lemma dpow_zero {x : S} (hx : x ∈ I.map (algebraMap A S)) : Localization.dpow δ M S 0 x = 1 := by
  obtain ⟨a, s, rfl⟩ := ideal_fraction M S hx
  rw [dpow_fraction δ M S 0 a.property, δ.dpow_zero a.property, pow_zero,
    IsLocalization.mk'_one, map_one]

lemma dpow_one {x : S} (hx : x ∈ I.map (algebraMap A S)) : Localization.dpow δ M S 1 x = x := by
  obtain ⟨a, s, rfl⟩ := ideal_fraction M S hx
  rw [dpow_fraction δ M S 1 a.property, δ.dpow_one a.property, pow_one]

lemma dpow_mem {n : ℕ} (hn : n ≠ 0) {x : S} (hx : x ∈ I.map (algebraMap A S)) :
    Localization.dpow δ M S n x ∈ I.map (algebraMap A S) := by
  obtain ⟨a, s, rfl⟩ := ideal_fraction M S hx
  rw [dpow_fraction δ M S n a.property]
  exact fraction_mem M S _ (δ.dpow_mem hn a.property) _

lemma dpow_add (n : ℕ) {x y : S} (hx : x ∈ I.map (algebraMap A S))
    (hy : y ∈ I.map (algebraMap A S)) :
    Localization.dpow δ M S n (x + y) =
      ∑ k ∈ Finset.HasAntidiagonal.antidiagonal n, Localization.dpow δ M S k.1 x * Localization.dpow δ M S k.2 y := by
  obtain ⟨a, b, s, rfl, rfl⟩ := ideal_pair_fraction M S hx hy
  rw [← fraction_add_same, dpow_fraction δ M S n (I.add_mem a.property b.property),
    δ.dpow_add a.property b.property, fraction_sum]
  apply Finset.sum_congr rfl
  intro k hk
  rw [dpow_fraction δ M S k.1 a.property, dpow_fraction δ M S k.2 b.property,
    ← IsLocalization.mk'_mul, ← pow_add, Finset.HasAntidiagonal.mem_antidiagonal.mp hk]

lemma dpow_mul (n : ℕ) (a : S) {x : S} (hx : x ∈ I.map (algebraMap A S)) :
    Localization.dpow δ M S n (a * x) = a ^ n * Localization.dpow δ M S n x := by
  obtain ⟨b, t, rfl⟩ := IsLocalization.exists_mk'_eq M a
  obtain ⟨c, s, rfl⟩ := ideal_fraction M S hx
  rw [← IsLocalization.mk'_mul, dpow_fraction δ M S n (I.mul_mem_left _ c.property),
    dpow_fraction δ M S n c.property, δ.dpow_mul c.property, mul_pow,
    IsLocalization.mk'_mul, IsLocalization.mk'_pow]

lemma mul_dpow (m n : ℕ) {x : S} (hx : x ∈ I.map (algebraMap A S)) :
    Localization.dpow δ M S m x * Localization.dpow δ M S n x = (Nat.choose (m + n) m : S) * Localization.dpow δ M S (m + n) x := by
  obtain ⟨a, s, rfl⟩ := ideal_fraction M S hx
  rw [dpow_fraction δ M S m a.property, dpow_fraction δ M S n a.property,
    dpow_fraction δ M S (m + n) a.property, ← IsLocalization.mk'_mul,
    ← pow_add, δ.mul_dpow a.property, ← IsLocalization.mul_mk'_eq_mk'_of_mul, map_natCast]

lemma dpow_comp (m n : ℕ) (hn : n ≠ 0) {x : S} (hx : x ∈ I.map (algebraMap A S)) :
    Localization.dpow δ M S m (Localization.dpow δ M S n x) = (Nat.uniformBell m n : S) * Localization.dpow δ M S (m * n) x := by
  obtain ⟨a, s, rfl⟩ := ideal_fraction M S hx
  rw [dpow_fraction δ M S n a.property,
    dpow_fraction δ M S m (δ.dpow_mem hn a.property),
    dpow_fraction δ M S (m * n) a.property, δ.dpow_comp hn a.property,
    ← pow_mul, Nat.mul_comm n m, ← IsLocalization.mul_mk'_eq_mk'_of_mul, map_natCast]

def dividedPowers : DividedPowers (I.map (algebraMap A S)) where
  dpow := Localization.dpow δ M S
  dpow_null hx := by
    classical
    exact dite_eq_right hx
  dpow_zero := Localization.dpow_zero δ M S
  dpow_one := Localization.dpow_one δ M S
  dpow_mem {n x} hn hx := Localization.dpow_mem δ M S hn hx
  dpow_add := Localization.dpow_add δ M S _
  dpow_mul := fun {n a x} hx => Localization.dpow_mul δ M S n a hx
  mul_dpow := Localization.mul_dpow δ M S _ _
  dpow_comp {m n _x} hn hx := Localization.dpow_comp δ M S m n hn hx

/-- The original ring maps to its localization as a divided-power ring. -/
def localizationMap : DividedPowers.DPMorphism δ (dividedPowers δ M S) where
  toRingHom := algebraMap A S
  ideal_comp := le_rfl
  dpow_comp {n} _x hx := dpow_algebraMap δ M S n hx

lemma fraction_power_denominator (x : A) (s : M) (n : ℕ) :
    IsLocalization.mk' S x (s ^ n) =
      algebraMap A S x * IsLocalization.mk' S 1 s ^ n := by
  rw [IsLocalization.mk'_eq_mul_mk'_one, ← IsLocalization.mk'_pow, one_pow]

variable {T : Type*} [CommRing T] {K : Ideal T} (ε : DividedPowers K)
variable (F : S →+* T)

/-- A ring map from a localization is compatible with divided powers as soon
as its restriction to the original ring is compatible. -/
def mapFromLocalization
    (hF : DividedPowers.IsDPMorphism δ ε (F.comp (algebraMap A S))) :
    DividedPowers.DPMorphism (dividedPowers δ M S) ε where
  toRingHom := F
  ideal_comp := by
    rw [Ideal.map_map]
    exact hF.ideal_comp
  dpow_comp {n} z hz := by
    obtain ⟨x, s, rfl⟩ := ideal_fraction M S hz
    have hx : F (algebraMap A S (x : A)) ∈ K :=
      hF.ideal_comp (Ideal.mem_map_of_mem _ x.property)
    change ε.dpow n (F (IsLocalization.mk' S (x : A) s)) =
      F (Localization.dpow δ M S n (IsLocalization.mk' S (x : A) s))
    rw [dpow_fraction δ M S n x.property]
    calc
      ε.dpow n (F (IsLocalization.mk' S (x : A) s)) =
          ε.dpow n (F (IsLocalization.mk' S 1 s) * F (algebraMap A S (x : A))) := by
        rw [IsLocalization.mk'_eq_mul_mk'_one (S := S) (x : A) s, map_mul, mul_comm]
      _ = F (IsLocalization.mk' S 1 s) ^ n * ε.dpow n (F (algebraMap A S (x : A))) :=
        ε.dpow_mul hx
      _ = F (IsLocalization.mk' S 1 s) ^ n * F (algebraMap A S (δ.dpow n (x : A))) := by
        exact congrArg (fun z => F (IsLocalization.mk' S 1 s) ^ n * z)
          (hF.dpow_comp (n := n) x x.property)
      _ = F (IsLocalization.mk' S (δ.dpow n (x : A)) (s ^ n)) := by
        rw [fraction_power_denominator, map_mul, map_pow, mul_comm]

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.DividedPower.Localization

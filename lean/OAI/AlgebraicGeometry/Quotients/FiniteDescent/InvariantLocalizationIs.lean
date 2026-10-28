import Mathlib.RingTheory.Localization.Away.Basic
import Mathlib.Algebra.Ring.Subring.Basic
import Mathlib.Algebra.Group.Submonoid.Units

/-! # Invariant Localization Is -/

namespace OAI.AlgebraicGeometry.Quotients.FiniteDescent.InvariantLocalizationIs.Construction.InvariantLocalization

/-!
# Localization of invariant rings

Taking the equalizer of two ring maps commutes with localization at an element
on which the maps agree. The proof clears denominators in the target ring;
it does not require either map or either localization to be injective.
-/

universe u v w z

variable {A : Type u} {B : Type v} {A' : Type w} {B' : Type z}
variable [CommRing A] [CommRing B] [CommRing A'] [CommRing B']
variable [Algebra A A'] [Algebra B B']

/-- Compatible ring maps induce a map on their invariant subrings. -/
def map (s t : A →+* B) (s' t' : A' →+* B')
    (hs : ∀ a, s' (algebraMap A A' a) = algebraMap B B' (s a))
    (ht : ∀ a, t' (algebraMap A A' a) = algebraMap B B' (t a)) :
    s.eqLocus t →+* s'.eqLocus t' :=
  ((algebraMap A A').comp (s.eqLocus t).subtype).codRestrict (s'.eqLocus t')
    (fun a => by
      change s' (algebraMap A A' (a : A)) = t' (algebraMap A A' (a : A))
      rw [hs, ht, a.property])

/-- Invariants commute with localization at an invariant element. -/
theorem away (s t : A →+* B) (s' t' : A' →+* B')
    (hs : ∀ a, s' (algebraMap A A' a) = algebraMap B B' (s a))
    (ht : ∀ a, t' (algebraMap A A' a) = algebraMap B B' (t a))
    (g : s.eqLocus t)
    [IsLocalization.Away (g : A) A'] [IsLocalization.Away (s (g : A)) B'] :
    letI := (map s t s' t' hs ht).toAlgebra
    IsLocalization.Away g (s'.eqLocus t') := by
  let C := s.eqLocus t
  let C' := s'.eqLocus t'
  let : Algebra C C' := (map s t s' t' hs ht).toAlgebra
  have hg : s (g : A) = t (g : A) := g.property
  apply IsLocalization.Away.mk
  · exact (MonoidHom.isUnit_eqLocusM_mk_iff s'.toMonoidHom t'.toMonoidHom
      ((map s t s' t' hs ht g).property)).mpr
        (IsLocalization.Away.algebraMap_isUnit (g : A))
  · intro z
    obtain ⟨n, a, ha⟩ := IsLocalization.Away.surj (g : A) (z : A')
    have hsa : algebraMap B B' (s a) = algebraMap B B' (t a) := by
      rw [← hs, ← ht, ← ha, map_mul, map_mul, map_pow, map_pow,
        hs, ht, g.property, z.property]
    obtain ⟨m, hm⟩ := IsLocalization.Away.exists_of_eq (s (g : A)) hsa
    have hmem : (g : A) ^ m * a ∈ C := by
      change s ((g : A) ^ m * a) = t ((g : A) ^ m * a)
      simpa only [map_mul, map_pow, ← hg] using hm
    refine ⟨n + m, ⟨(g : A) ^ m * a, hmem⟩, ?_⟩
    apply Subtype.ext
    change (z : A') * algebraMap A A' (g : A) ^ (n + m) =
      algebraMap A A' ((g : A) ^ m * a)
    rw [pow_add, ← mul_assoc, ha, map_mul, map_pow, mul_comm]
  · intro a b hab
    have h : algebraMap A A' (a : A) = algebraMap A A' (b : A) :=
      congrArg Subtype.val hab
    obtain ⟨n, hn⟩ := IsLocalization.Away.exists_of_eq (g : A) h
    exact ⟨n, Subtype.ext hn⟩

noncomputable def awayMap (f : A →+* B) (a : A) (b : B) (h : f a = b) :
    Localization.Away a →+* Localization.Away b :=
  IsLocalization.Away.lift a (g := (algebraMap B (Localization.Away b)).comp f)
    (by simpa only [RingHom.comp_apply, h] using
      (IsLocalization.Away.algebraMap_isUnit (S := Localization.Away b) b))

@[simp]
theorem awayMap_algebraMap (f : A →+* B) (a : A) (b : B) (h : f a = b) (x : A) :
    awayMap f a b h (algebraMap A (Localization.Away a) x) =
      algebraMap B (Localization.Away b) (f x) :=
  IsLocalization.Away.lift_eq _ _ _

/-- An injective ring map remains injective after localizing source and target
at corresponding elements. -/
theorem awayMap_injective (f : A →+* B) (a : A) (b : B) (h : f a = b)
    (hf : Function.Injective f) : Function.Injective (awayMap f a b h) := by
  apply IsLocalization.injective_of_map_algebraMap_zero (M := Submonoid.powers a)
    (Localization.Away a) (awayMap f a b h)
  intro x hx
  rw [awayMap_algebraMap, ← map_zero (algebraMap B (Localization.Away b))] at hx
  obtain ⟨n, hn⟩ := IsLocalization.Away.exists_of_eq b hx
  have hzero : a ^ n * x = 0 := by
    apply hf
    simpa only [map_mul, map_pow, h, map_zero, mul_zero] using hn
  rw [← map_zero (algebraMap A (Localization.Away a))]
  apply (IsLocalization.eq_iff_exists (Submonoid.powers a) (Localization.Away a)).mpr
  exact ⟨⟨a ^ n, n, rfl⟩, by simpa only [mul_zero] using hzero⟩

noncomputable abbrev awayInvariants (s t : A →+* B) (g : s.eqLocus t) :
    Subring (Localization.Away (g : A)) :=
  (awayMap s (g : A) (s (g : A)) rfl).eqLocus
    (awayMap t (g : A) (s (g : A)) g.property.symm)

/-- The natural map from invariants to localized invariants. -/
noncomputable def awayInvariantMap (s t : A →+* B) (g : s.eqLocus t) :
    s.eqLocus t →+* awayInvariants s t g :=
  map s t (awayMap s (g : A) (s (g : A)) rfl)
    (awayMap t (g : A) (s (g : A)) g.property.symm)
    (awayMap_algebraMap s (g : A) (s (g : A)) rfl)
    (awayMap_algebraMap t (g : A) (s (g : A)) g.property.symm)

/-- The canonical localized invariant ring is a localization of the original
invariant ring, with its natural map. -/
theorem isLocalization_awayInvariants (s t : A →+* B) (g : s.eqLocus t) :
    letI := (awayInvariantMap s t g).toAlgebra
    IsLocalization.Away g (awayInvariants s t g) :=
  away s t _ _ (awayMap_algebraMap s (g : A) (s (g : A)) rfl)
    (awayMap_algebraMap t (g : A) (s (g : A)) g.property.symm) g

/-- The original and localized invariant inclusions give the same scalar action. -/
theorem scalarTower_awayInvariants (s t : A →+* B) (g : s.eqLocus t) :
    let C := s.eqLocus t
    let C₁ := awayInvariants s t g
    letI : Algebra C A := C.subtype.toAlgebra
    letI : Algebra C C₁ := (awayInvariantMap s t g).toAlgebra
    letI : Algebra C₁ (Localization.Away (g : A)) := C₁.subtype.toAlgebra
    IsScalarTower C C₁ (Localization.Away (g : A)) := by
  let C := s.eqLocus t
  let C₁ := awayInvariants s t g
  let : Algebra C A := C.subtype.toAlgebra
  let : Algebra C C₁ := (awayInvariantMap s t g).toAlgebra
  let : Algebra C₁ (Localization.Away (g : A)) := C₁.subtype.toAlgebra
  apply IsScalarTower.of_algebraMap_eq
  intro a
  rw [IsScalarTower.algebraMap_apply C A (Localization.Away (g : A))]
  rfl

end OAI.AlgebraicGeometry.Quotients.FiniteDescent.InvariantLocalizationIs.Construction.InvariantLocalization

import Mathlib.RingTheory.NoetherNormalization
import Mathlib.RingTheory.DedekindDomain.IntegralClosure
import Mathlib.RingTheory.Polynomial.UniqueFactorization
import Mathlib.RingTheory.Localization.Finiteness

/-! # Normalization -/

namespace OAI.AlgebraicGeometry.CycleClass.Thom.Finite.Normalization.Constructions

noncomputable section

/-!
# ThomClass: finiteness of normalization in characteristic zero

Noether normalization reduces finiteness to the trace-dual lattice bound
over a normal polynomial ring. These are constructions on actual integral
closures, to be applied to affine charts of the integral cycle supports.
-/

theorem finite_fraction_extension
    (A B K L : Type*) [CommRing A] [CommRing B] [IsDomain A] [IsDomain B]
    [Field K] [Field L] [Algebra A B] [Module.Finite A B]
    [Algebra A K] [IsFractionRing A K] [Algebra A L] [Algebra B L]
    [IsFractionRing B L] [IsScalarTower A B L]
    [Algebra K L] [IsScalarTower A K L]
    (hi : Function.Injective (algebraMap A L)) : Module.Finite K L := by
  classical
  obtain ⟨s, hs⟩ := Module.Finite.fg_top (R := A) (M := B)
  apply Module.Finite.of_fg_top
  refine ⟨s.image (algebraMap B L), ?_⟩
  apply top_unique
  intro x _
  have hx := IsFractionRing.ideal_span_singleton_map_subset (R := A) (K := K)
    (S := B) (L := L) (a := 1) (b := (s : Set B)) hi
    (by rw [hs]; exact Set.subset_univ _)
    (show x ∈ (Ideal.span ({algebraMap B L 1} : Set L) : Set L) by simp)
  simpa only [Finset.coe_image, SetLike.mem_coe] using hx

/-- Finite algebras over a normal Noetherian characteristic-zero domain
have finite normalization in their fraction field. -/
theorem finite_integralClosure_over_normal
    (A B L : Type*) [CommRing A] [CommRing B] [IsDomain A] [IsDomain B]
    [IsNoetherianRing A] [IsIntegrallyClosed A] [CharZero A]
    [Field L] [Algebra A B] [Module.Finite A B]
    [Algebra A L] [Algebra B L] [IsFractionRing B L] [IsScalarTower A B L]
    (hi : Function.Injective (algebraMap A L)) :
    Module.Finite B (integralClosure B L) := by
  let : FaithfulSMul A L := (faithfulSMul_iff_algebraMap_injective A L).mpr hi
  let : Algebra (FractionRing A) L := FractionRing.liftAlgebra A L
  let : Module.Finite (FractionRing A) L :=
    finite_fraction_extension A B (FractionRing A) L hi
  let : IsIntegralClosure (integralClosure B L) A L :=
    ⟨IsIntegralClosure.algebraMap_injective (integralClosure B L) B L,
      fun {x} => ⟨fun hx =>
        (IsIntegralClosure.isIntegral_iff (A := integralClosure B L) (R := B)).mp
          (show IsIntegral B x from hx.tower_top),
        fun hx => isIntegral_trans (R := A) x
          ((IsIntegralClosure.isIntegral_iff (A := integralClosure B L) (R := B)).mpr hx)⟩⟩
  let : Module.Finite A (integralClosure B L) :=
    IsIntegralClosure.finite A (FractionRing A) L (integralClosure B L)
  exact Module.Finite.of_restrictScalars_finite A B (integralClosure B L)

/-- Normalization of a finite-type domain over a characteristic-zero field
is a finite module over that domain. -/
theorem finite_integralClosure
    (k B L : Type*) [Field k] [CharZero k] [CommRing B] [IsDomain B]
    [Algebra k B] [Algebra.FiniteType k B]
    [Field L] [Algebra B L] [IsFractionRing B L] :
    Module.Finite B (integralClosure B L) := by
  obtain ⟨n, g, hi, hf⟩ := exists_finite_inj_algHom_of_fg k B
  let A := MvPolynomial (Fin n) k
  let : Algebra A B := g.toRingHom.toAlgebra
  let : Module.Finite A B := hf
  let : Algebra A L := ((algebraMap B L).comp g.toRingHom).toAlgebra
  let : IsScalarTower A B L := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  exact finite_integralClosure_over_normal A B L
    ((IsFractionRing.injective B L).comp hi)

/-- Finiteness persists on the local rings of affine finite-type charts. -/
theorem finite_integralClosure_localization
    (k B R L : Type*) [Field k] [CharZero k] [CommRing B] [IsDomain B]
    [Algebra k B] [Algebra.FiniteType k B]
    [CommRing R] [Algebra B R] (M : Submonoid B) [IsLocalization M R]
    [Field L] [Algebra B L] [Algebra R L] [IsScalarTower B R L]
    [IsFractionRing B L] : Module.Finite R (integralClosure R L) := by
  let C := integralClosure B L
  let D := integralClosure R L
  have hCD : C ≤ D.restrictScalars B := fun _ hx => hx.tower_top
  let i : C →ₐ[B] D := Subalgebra.inclusion hCD
  let : Algebra C D := i.toRingHom.toAlgebra
  let : IsScalarTower B C D := IsScalarTower.of_algHom i
  let : IsScalarTower C D L := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  let : Module.Finite B C := finite_integralClosure k B L
  let : IsLocalization (Algebra.algebraMapSubmonoid L M) L :=
    IsLocalization.of_le_isUnit (fun x hx => by
      obtain ⟨m, hm, rfl⟩ := hx
      have h := (IsLocalization.map_units R (⟨m, hm⟩ : M)).map (algebraMap R L)
      change IsUnit (algebraMap B L m)
      simpa only [← IsScalarTower.algebraMap_apply] using h)
  let : IsLocalization (Algebra.algebraMapSubmonoid C M) D :=
    IsLocalization.integralClosure M
  exact Module.Finite.of_isLocalization B C M

end

end OAI.AlgebraicGeometry.CycleClass.Thom.Finite.Normalization.Constructions

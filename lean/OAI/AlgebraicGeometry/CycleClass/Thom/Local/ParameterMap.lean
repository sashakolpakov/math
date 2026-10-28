import OAI.AlgebraicGeometry.CycleClass.Thom.SmoothLocalFiber
import Mathlib.RingTheory.Artinian.Algebra
import Mathlib.RingTheory.Algebraic.Integral
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.Polynomial.UniqueFactorization

/-! # Parameter Map -/

namespace OAI.AlgebraicGeometry.CycleClass.Thom.Local.ParameterMap.Constructions

noncomputable section

/-! The actual polynomial parameter map into a local domain, localized
at the inverse image of its maximal ideal. -/

open _root_.Algebra _root_.Polynomial IsLocalRing

variable (k R : Type*) [Field k] [CommRing R] [IsLocalRing R] [Algebra k R]
  (t : R)

def parameterPrime : Ideal k[X] := (maximalIdeal R).comap (aeval t).toRingHom

instance parameterPrime_isPrime : (parameterPrime k R t).IsPrime :=
  Ideal.IsPrime.comap (aeval t).toRingHom

abbrev parameterStalk := Localization.AtPrime (parameterPrime k R t)

def parameterMap : parameterStalk k R t →ₐ[k] R :=
  IsLocalization.liftAlgHom (M := (parameterPrime k R t).primeCompl) (f := aeval t)
    (fun s => by
      have h := s.property
      change ¬ ¬ IsUnit (aeval t s.val) at h
      exact Classical.not_not.mp h)

theorem parameterMap_algebraMap (a : k[X]) :
    parameterMap k R t (algebraMap k[X] (parameterStalk k R t) a) = aeval t a :=
  IsLocalization.lift_eq _ _

instance parameterMap_isLocalHom : IsLocalHom (parameterMap k R t).toRingHom := by
  apply IsLocalHom.mk
  intro x hx
  obtain ⟨a, b, rfl⟩ := IsLocalization.exists_mk'_eq (parameterPrime k R t).primeCompl x
  rw [IsLocalization.AtPrime.isUnit_mk'_iff]
  have hmul : parameterMap k R t (IsLocalization.mk' (parameterStalk k R t) a b) *
      aeval t (b : k[X]) = aeval t a := by
    rw [← parameterMap_algebraMap k R t, ← map_mul, IsLocalization.mk'_spec,
      parameterMap_algebraMap]
  have hb : IsUnit (aeval t (b : k[X])) := by
    have h := b.property
    change ¬ ¬ IsUnit (aeval t (b : k[X])) at h
    exact Classical.not_not.mp h
  change ¬ ¬ IsUnit (aeval t a)
  exact not_not.mpr (hmul ▸ hx.mul hb)

theorem parameterPrime_eq_span (ht : t ∈ maximalIdeal R) :
    parameterPrime k R t = Ideal.span {Polynomial.X} := by
  have hm : (Ideal.span ({Polynomial.X} : Set k[X])).IsMaximal :=
    PrincipalIdealRing.isMaximal_of_irreducible (irreducible_X (R := k))
  apply ((hm.eq_iff_le (Ideal.IsPrime.ne_top inferInstance)).mpr ?_).symm
  rw [Ideal.span_singleton_le_iff_mem]
  change aeval t Polynomial.X ∈ maximalIdeal R
  simpa only [aeval_X] using ht

theorem parameterMap_maximalIdeal (ht : t ∈ maximalIdeal R) :
    (maximalIdeal (parameterStalk k R t)).map (parameterMap k R t).toRingHom =
      Ideal.span {t} := by
  rw [← Localization.AtPrime.map_eq_maximalIdeal, Ideal.map_map]
  have hm : (parameterMap k R t).toRingHom.comp
      (algebraMap k[X] (parameterStalk k R t)) = (aeval t).toRingHom :=
    RingHom.ext (parameterMap_algebraMap k R t)
  rw [hm, parameterPrime_eq_span k R t ht, Ideal.map_span, Set.image_singleton]
  simp only [AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom, aeval_X]

omit [IsLocalRing R] in
theorem parameter_transcendental [IsDomain R] (ht : t ≠ 0) (hu : ¬ IsUnit t) :
    Transcendental k t := by
  intro h
  exact hu (IsArtinianRing.isUnit_of_isIntegral_of_nonZeroDivisor h.isIntegral
    (mem_nonZeroDivisors_of_ne_zero ht))

theorem parameterMap_injective [IsDomain R] (ht : t ≠ 0) (hu : ¬ IsUnit t) :
    Function.Injective (parameterMap k R t) := by
  apply (IsLocalization.injective_iff_map_algebraMap_eq
    (parameterPrime k R t).primeCompl (parameterMap k R t).toRingHom).mpr
  intro a b
  change algebraMap k[X] (parameterStalk k R t) a =
    algebraMap k[X] (parameterStalk k R t) b ↔
      parameterMap k R t (algebraMap k[X] (parameterStalk k R t) a) =
        parameterMap k R t (algebraMap k[X] (parameterStalk k R t) b)
  rw [parameterMap_algebraMap, parameterMap_algebraMap]
  have ha : Function.Injective (algebraMap k[X] (parameterStalk k R t)) :=
    IsLocalization.injective _ (parameterPrime k R t).primeCompl_le_nonZeroDivisors
  rw [ha.eq_iff, (transcendental_iff_injective.mp
    (parameter_transcendental k R t ht hu)).eq_iff]

end

end OAI.AlgebraicGeometry.CycleClass.Thom.Local.ParameterMap.Constructions

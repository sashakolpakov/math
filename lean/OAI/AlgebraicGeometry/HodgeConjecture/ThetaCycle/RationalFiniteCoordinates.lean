import OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.FieldAdelicCharacter
import Mathlib.NumberTheory.Padics.HeightOneSpectrum

/-! # Rational Finite Coordinates -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.RationalFiniteCoordinates.CM

noncomputable section

/-! ThetaCycle: compare the two actual finite-adele models over the rationals,
using their common p-adic completions and integral subrings. -/

open scoped Classical _root_.NumberField
open _root_.NumberField IsDedekindDomain Filter

local instance (p : Nat.Primes) : Fact p.val.Prime := ⟨p.property⟩

def rationalFinitePlaceEquiv : HeightOneSpectrum (𝓞 ℚ) ≃ HeightOneSpectrum ℤ :=
  (Rat.HeightOneSpectrum.primesEquiv (R := 𝓞 ℚ)).trans
    (Rat.HeightOneSpectrum.primesEquiv (R := ℤ)).symm

def rationalFiniteLocalEquiv (v : HeightOneSpectrum ℤ) :
    (rationalFinitePlaceEquiv.symm v).adicCompletion ℚ ≃+* v.adicCompletion ℚ :=
  (Padic.adicCompletionEquiv (𝓞 ℚ) (Rat.HeightOneSpectrum.primesEquiv v)).symm.toRingEquiv.trans
    (Rat.HeightOneSpectrum.adicCompletion.padicEquiv v).symm.toRingEquiv

theorem rational_finite_local_equiv_apply (v : HeightOneSpectrum ℤ)
    (x : (rationalFinitePlaceEquiv.symm v).adicCompletion ℚ) :
    rationalFiniteLocalEquiv v x =
      (Rat.HeightOneSpectrum.adicCompletion.padicEquiv v).symm
        ((Padic.adicCompletionEquiv (𝓞 ℚ) (Rat.HeightOneSpectrum.primesEquiv v)).symm x) :=
  RingEquiv.trans_apply _ _ x

theorem padic_cast_symm_integral {p q : Nat.Primes} (h : p = q) (x : Padic q) :
    (ContinuousAlgEquiv.cast (R := ℚ) (A := fun r : Nat.Primes => Padic r) h).symm x ∈
      PadicInt.subring p ↔ x ∈ PadicInt.subring q := by
  subst q
  rfl

theorem rational_local_padic_integral {R : Type*} [CommRing R] [Algebra R ℚ]
    [IsIntegralClosure R ℤ ℚ] [IsDedekindDomain R] [IsFractionRing R ℚ]
    (v : HeightOneSpectrum R) (x : v.adicCompletion ℚ) :
    Rat.HeightOneSpectrum.adicCompletion.padicEquiv v x ∈
      PadicInt.subring (Rat.HeightOneSpectrum.primesEquiv v) ↔ x ∈ v.adicCompletionIntegers ℚ := by
  have hb := Rat.HeightOneSpectrum.adicCompletion.padicEquiv_bijOn v
  constructor
  · intro hx
    obtain ⟨y, hy, he⟩ := hb.surjOn hx
    exact (Rat.HeightOneSpectrum.adicCompletion.padicEquiv v).injective he ▸ hy
  · intro hx
    exact hb.mapsTo hx

theorem rational_local_padic_integral_inv {R : Type*} [CommRing R] [Algebra R ℚ]
    [IsIntegralClosure R ℤ ℚ] [IsDedekindDomain R] [IsFractionRing R ℚ]
    (v : HeightOneSpectrum R) (x : Padic (Rat.HeightOneSpectrum.primesEquiv v)) :
    (Rat.HeightOneSpectrum.adicCompletion.padicEquiv v).symm x ∈ v.adicCompletionIntegers ℚ ↔
      x ∈ PadicInt.subring (Rat.HeightOneSpectrum.primesEquiv v) := by
  rw [← rational_local_padic_integral v, ContinuousAlgEquiv.apply_symm_apply]

theorem rational_padic_inverse_integral (p : Nat.Primes)
    (x : ((Rat.HeightOneSpectrum.primesEquiv (R := 𝓞 ℚ)).symm p).adicCompletion ℚ) :
    (Padic.adicCompletionEquiv (𝓞 ℚ) p).symm x ∈ PadicInt.subring p ↔
      x ∈ ((Rat.HeightOneSpectrum.primesEquiv (R := 𝓞 ℚ)).symm p).adicCompletionIntegers ℚ := by
  unfold Padic.adicCompletionEquiv
  rw [ContinuousAlgEquiv.symm_trans_apply, ContinuousAlgEquiv.symm_symm,
    padic_cast_symm_integral, rational_local_padic_integral]

theorem rational_finite_local_integral (v : HeightOneSpectrum ℤ)
    (x : (rationalFinitePlaceEquiv.symm v).adicCompletion ℚ) :
    rationalFiniteLocalEquiv v x ∈ v.adicCompletionIntegers ℚ ↔
      x ∈ (rationalFinitePlaceEquiv.symm v).adicCompletionIntegers ℚ := by
  rw [rational_finite_local_equiv_apply]
  exact (rational_local_padic_integral_inv v _).trans (rational_padic_inverse_integral _ x)

def rationalFiniteLocalMap (v : HeightOneSpectrum ℤ) :
    (rationalFinitePlaceEquiv.symm v).adicCompletion ℚ →+* v.adicCompletion ℚ :=
  (rationalFiniteLocalEquiv v).toRingHom

theorem rational_finite_local_map_continuous (v : HeightOneSpectrum ℤ) :
    Continuous (rationalFiniteLocalMap v) :=
  (Rat.HeightOneSpectrum.adicCompletion.padicEquiv v).symm.continuous.comp
    (Padic.adicCompletionEquiv (𝓞 ℚ) (Rat.HeightOneSpectrum.primesEquiv v)).symm.continuous

theorem rational_finite_local_map_principal (v : HeightOneSpectrum ℤ) (q : ℚ) :
    rationalFiniteLocalMap v (algebraMap ℚ ((rationalFinitePlaceEquiv.symm v).adicCompletion ℚ) q) =
      algebraMap ℚ (v.adicCompletion ℚ) q :=
  (rationalFiniteLocalMap v).map_rat_algebraMap q

theorem rational_finite_map_integral : ∀ᶠ v : HeightOneSpectrum ℤ in cofinite,
    Set.MapsTo (rationalFiniteLocalMap v)
      ((rationalFinitePlaceEquiv.symm v).adicCompletionIntegers ℚ) (v.adicCompletionIntegers ℚ) :=
  Eventually.of_forall (fun v x hx => (rational_finite_local_integral v x).mpr hx)

def rationalFiniteAdeleFunction : RepresentationTheory.Weil.AdelicSplitting.ArchimedeanAdeles.Construction.FiniteAdeles ℚ → RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQf :=
  RestrictedProduct.mapAlong
    (fun v : HeightOneSpectrum (𝓞 ℚ) => v.adicCompletion ℚ)
    (fun v : HeightOneSpectrum ℤ => v.adicCompletion ℚ)
    rationalFinitePlaceEquiv.symm rationalFinitePlaceEquiv.symm.injective.tendsto_cofinite
    (fun v => rationalFiniteLocalMap v) rational_finite_map_integral

theorem rational_finite_adele_function_continuous : Continuous rationalFiniteAdeleFunction :=
  RestrictedProduct.mapAlong_continuous
    (fun v : HeightOneSpectrum (𝓞 ℚ) => v.adicCompletion ℚ)
    (fun v : HeightOneSpectrum ℤ => v.adicCompletion ℚ)
    rationalFinitePlaceEquiv.symm rationalFinitePlaceEquiv.symm.injective.tendsto_cofinite
    (fun v => rationalFiniteLocalMap v) rational_finite_map_integral
    rational_finite_local_map_continuous

def rationalFiniteAdeleMap : RepresentationTheory.Weil.AdelicSplitting.ArchimedeanAdeles.Construction.FiniteAdeles ℚ →+* RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQf where
  toFun := rationalFiniteAdeleFunction
  map_zero' := by
    apply FiniteAdeleRing.ext
    intro v
    exact map_zero (rationalFiniteLocalMap v)
  map_one' := by
    apply FiniteAdeleRing.ext
    intro v
    exact map_one (rationalFiniteLocalMap v)
  map_add' a b := by
    apply FiniteAdeleRing.ext
    intro v
    exact map_add (rationalFiniteLocalMap v) _ _
  map_mul' a b := by
    apply FiniteAdeleRing.ext
    intro v
    exact map_mul (rationalFiniteLocalMap v) _ _

theorem rational_finite_adele_map_apply (a : RepresentationTheory.Weil.AdelicSplitting.ArchimedeanAdeles.Construction.FiniteAdeles ℚ) (v : HeightOneSpectrum ℤ) :
    rationalFiniteAdeleMap a v = rationalFiniteLocalEquiv v (a (rationalFinitePlaceEquiv.symm v)) := rfl

theorem rational_finite_adele_map_continuous : Continuous rationalFiniteAdeleMap :=
  rational_finite_adele_function_continuous

theorem rational_finite_adele_map_principal (q : ℚ) :
    rationalFiniteAdeleMap (algebraMap ℚ (RepresentationTheory.Weil.AdelicSplitting.ArchimedeanAdeles.Construction.FiniteAdeles ℚ) q) = algebraMap ℚ RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQf q :=
  rationalFiniteAdeleMap.map_rat_algebraMap q

theorem rational_finite_character_comparison (a : RepresentationTheory.Weil.AdelicSplitting.ArchimedeanAdeles.Construction.FiniteAdeles ℚ) :
    AdelicCharacter.CM.finiteStandardCharacter (rationalFiniteAdeleMap a) = FieldAdelicCharacter.CM.fieldFiniteCharacter ℚ a := by
  have he := (RepresentationTheory.Weil.AdelicSplitting.StrongApproximation.Construction.denseRange_rational_finiteAdeles ℚ).equalizer
    (AdelicCharacter.CM.finite_standard_character_locallyConstant.continuous.comp rational_finite_adele_map_continuous)
    (FieldAdelicCharacter.CM.field_finite_character_locallyConstant ℚ).continuous (funext fun q => by
      change AdelicCharacter.CM.finiteStandardCharacter (rationalFiniteAdeleMap (algebraMap ℚ (RepresentationTheory.Weil.AdelicSplitting.ArchimedeanAdeles.Construction.FiniteAdeles ℚ) q)) =
        FieldAdelicCharacter.CM.fieldFiniteCharacter ℚ (algebraMap ℚ (RepresentationTheory.Weil.AdelicSplitting.ArchimedeanAdeles.Construction.FiniteAdeles ℚ) q)
      have ht : Algebra.trace ℚ ℚ q = q := Algebra.trace_self_apply q
      rw [rational_finite_adele_map_principal, AdelicCharacter.CM.finite_standard_character_rational,
        FieldAdelicCharacter.CM.field_finite_character_rational]
      exact congrArg (fun t : ℚ => RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.standardRealCharacter (-(t : ℝ))) ht.symm)
  exact congrFun he a

end

end OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.RationalFiniteCoordinates.CM

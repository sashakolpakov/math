import Mathlib.RingTheory.RegularLocalRing.Polynomial
import Mathlib.RingTheory.Unramified.LocalRing
import Mathlib.RingTheory.Smooth.Flat

/-! # Etale Regular -/

namespace OAI.ArithmeticGeometry.OrdinaryLocus.Openness.EtaleRegular.Construction

noncomputable section

/-! Regularity across flat unramified local maps for the Openness dimension argument. -/

open IsLocalRing

/-- A flat local map cannot decrease Krull dimension. -/
theorem ringKrullDim_le_of_flat_local
    (R B : Type*) [CommRing R] [CommRing B] [Algebra R B]
    [IsLocalRing R] [IsLocalRing B] [IsNoetherianRing R] [IsNoetherianRing B]
    [IsLocalHom (algebraMap R B)] [Module.Flat R B] :
    ringKrullDim R ≤ ringKrullDim B := by
  have : (maximalIdeal B).LiesOver (maximalIdeal R) := by
    constructor
    exact (IsLocalRing.maximalIdeal_comap (algebraMap R B)).symm
  have h := Ideal.height_eq_height_add_of_liesOver_of_hasGoingDown
    (maximalIdeal R) (maximalIdeal B)
  have hle : (maximalIdeal R).height ≤ (maximalIdeal B).height := by
    rw [h]
    exact le_add_right le_rfl
  have hc := WithBot.coe_le_coe.mpr hle
  simpa only [maximalIdeal_height_eq_ringKrullDim] using hc

/-- Flat unramified local extensions of regular local rings are regular.
Unramifiedness bounds the generators of the maximal ideal, and flatness
supplies the opposite dimension inequality. -/
theorem isRegularLocalRing_of_flat_unramified
    (R B : Type*) [CommRing R] [CommRing B] [Algebra R B]
    [IsRegularLocalRing R] [IsLocalRing B] [IsNoetherianRing B]
    [IsLocalHom (algebraMap R B)] [Module.Flat R B]
    [Algebra.EssFiniteType R B] [Algebra.FormallyUnramified R B] :
    IsRegularLocalRing B := by
  apply IsRegularLocalRing.of_spanFinrank_maximalIdeal_le
  have hgen : (maximalIdeal B).spanFinrank ≤ (maximalIdeal R).spanFinrank := by
    rw [← Algebra.FormallyUnramified.map_maximalIdeal (R := R) (S := B)]
    exact Ideal.spanFinrank_map_le_of_fg _ (maximalIdeal R).fg_of_isNoetherianRing
  calc
    ((maximalIdeal B).spanFinrank : WithBot ℕ∞) ≤ (maximalIdeal R).spanFinrank := by
      exact_mod_cast hgen
    _ = ringKrullDim R := IsRegularLocalRing.spanFinrank_maximalIdeal
    _ ≤ ringKrullDim B := ringKrullDim_le_of_flat_local R B

/-- Etale algebras over regular rings are regular. -/
theorem isRegularRing_of_etale
    (R B : Type*) [CommRing R] [CommRing B] [Algebra R B]
    [IsRegularRing R] [Algebra.Etale R B] : IsRegularRing B := by
  have : IsNoetherianRing B := Algebra.FiniteType.isNoetherianRing R B
  apply isRegularRing_iff.mpr
  intro q hq
  let p := q.under R
  let := Localization.AtPrime.algebraOfLiesOver p q
  have : Algebra.EssFiniteType (Localization.AtPrime p) (Localization.AtPrime q) :=
    Algebra.EssFiniteType.of_comp R (Localization.AtPrime p) (Localization.AtPrime q)
  have : Algebra.FormallyUnramified R (Localization.AtPrime q) :=
    Algebra.FormallyUnramified.comp R B (Localization.AtPrime q)
  have : Algebra.FormallyUnramified (Localization.AtPrime p) (Localization.AtPrime q) :=
    Algebra.FormallyUnramified.of_restrictScalars R (Localization.AtPrime p) (Localization.AtPrime q)
  exact isRegularLocalRing_of_flat_unramified (Localization.AtPrime p) (Localization.AtPrime q)

end

end OAI.ArithmeticGeometry.OrdinaryLocus.Openness.EtaleRegular.Construction

import Mathlib.RingTheory.Flat.FaithfullyFlat.Algebra
import Mathlib.RingTheory.Flat.Localization
import Mathlib.RingTheory.Localization.AtPrime.Basic

/-! # Flat Ideal Descent -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups.Pointed.FlatIdealDescent.Construction

noncomputable section

/-! Equality of center ideals descends through a pointed flat comparison. -/

variable {R S : Type*} [CommRing R] [CommRing S] [Algebra R S] [Module.Flat R S]

/-- At any prime of a flat comparison chart, equality of extended ideals
reflects equality in the original local ring. -/
theorem flat_ideal_equality_reflects_at_prime (J K : Ideal R) (Q : Ideal S) [Q.IsPrime]
    (h : J.map (algebraMap R S) = K.map (algebraMap R S)) :
    J.map (algebraMap R (Localization.AtPrime (Q.under R))) =
      K.map (algebraMap R (Localization.AtPrime (Q.under R))) := by
  let q := Q.under R
  let : Algebra (Localization.AtPrime q) (Localization.AtPrime Q) :=
    Localization.AtPrime.algebraOfLiesOver q Q
  let : IsLocalHom (algebraMap (Localization.AtPrime q) (Localization.AtPrime Q)) := by
    rw [RingHom.algebraMap_toAlgebra]
    exact Localization.isLocalHom_localRingHom q Q (algebraMap R S) Ideal.LiesOver.over
  let : Module.FaithfullyFlat (Localization.AtPrime q) (Localization.AtPrime Q) :=
    Module.FaithfullyFlat.of_flat_of_isLocalHom
  apply Ideal.map_injective_of_faithfullyFlat (B := Localization.AtPrime Q)
  rw [Ideal.map_map, Ideal.map_map, ← IsScalarTower.algebraMap_eq]
  have hm := congrArg (Ideal.map (algebraMap S (Localization.AtPrime Q))) h
  rw [Ideal.map_map, Ideal.map_map, ← IsScalarTower.algebraMap_eq] at hm
  exact hm

end

end OAI.AlgebraicGeometry.Resolution.Blowups.Pointed.FlatIdealDescent.Construction

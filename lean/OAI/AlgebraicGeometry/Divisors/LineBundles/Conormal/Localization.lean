import Mathlib.RingTheory.Ideal.Cotangent
import Mathlib.RingTheory.Localization.Ideal
import Mathlib.Algebra.Module.LocalizedModule.IsLocalization

/-! # Localization -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.Conormal.Localization.BundleCycles

noncomputable section

/-! # LineBundleCycles: the actual conormal module commutes with base localization -/

variable {R : Type} [CommRing R] (I : Ideal R) (M : Submonoid R)
    (S : Type) [CommRing S] [Algebra R S] [IsLocalization M S]

def conormalLocalizationMap : I.Cotangent →ₗ[R] (I.map (algebraMap R S)).Cotangent :=
  Ideal.mapCotangent I (I.map (algebraMap R S)) (Algebra.ofId R S)
    (fun _ h => Ideal.mem_map_of_mem _ h)

theorem conormalLocalizationMap_toCotangent (a : I) :
    conormalLocalizationMap I S (I.toCotangent a) =
      (I.map (algebraMap R S)).toCotangent ⟨algebraMap R S a.val, Ideal.mem_map_of_mem _ a.property⟩ := rfl

instance conormalLocalizationMap_isLocalizedModule : IsLocalizedModule M (conormalLocalizationMap I S) where
  map_units m := by
    apply (Module.End.isUnit_iff _).mpr
    have h : Function.Bijective (fun x : (I.map (algebraMap R S)).Cotangent =>
        algebraMap R S m.val • x) := (IsLocalization.map_units S m).smul_bijective
    change Function.Bijective (fun x : (I.map (algebraMap R S)).Cotangent => m.val • x)
    simpa only [algebraMap_smul] using h
  surj a := by
    obtain ⟨a, rfl⟩ := (I.map (algebraMap R S)).toCotangent_surjective a
    obtain ⟨⟨r, m⟩, hr⟩ := (IsLocalization.mem_map_algebraMap_iff M S).mp a.property
    refine ⟨⟨I.toCotangent r, m⟩, ?_⟩
    change m.val • (I.map (algebraMap R S)).toCotangent a = conormalLocalizationMap I S (I.toCotangent r)
    rw [conormalLocalizationMap_toCotangent, ← algebraMap_smul S m.val,
      ← map_smul]
    apply congrArg (I.map (algebraMap R S)).toCotangent
    apply Subtype.ext
    exact (mul_comm (algebraMap R S m.val) a.val).trans hr
  exists_of_eq {a b} hab := by
    obtain ⟨a, rfl⟩ := I.toCotangent_surjective a
    obtain ⟨b, rfl⟩ := I.toCotangent_surjective b
    rw [conormalLocalizationMap_toCotangent, conormalLocalizationMap_toCotangent,
      Ideal.toCotangent_eq] at hab
    change algebraMap R S a.val - algebraMap R S b.val ∈ (I.map (algebraMap R S)) ^ 2 at hab
    rw [← map_sub, ← Ideal.map_pow, IsLocalization.algebraMap_mem_map_algebraMap_iff M S] at hab
    obtain ⟨m, hm, hab⟩ := hab
    refine ⟨⟨m, hm⟩, ?_⟩
    change m • I.toCotangent a = m • I.toCotangent b
    rw [← map_smul, ← map_smul, Ideal.toCotangent_eq]
    change m * a.val - m * b.val ∈ I ^ 2
    rw [← mul_sub]
    exact hab

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.Conormal.Localization.BundleCycles

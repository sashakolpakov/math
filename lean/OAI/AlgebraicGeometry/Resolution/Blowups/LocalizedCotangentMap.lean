import OAI.AlgebraicGeometry.Resolution.Blowups.FlatCotangentBaseChange
import Mathlib.RingTheory.Localization.BaseChange
import Mathlib.RingTheory.Flat.Localization

/-! # Localized Cotangent Map -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups.LocalizedCotangentMap.Construction

noncomputable section

/-! The conormal map of an actual localized ideal is the module localization map. -/

open scoped TensorProduct

variable {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]

def extendedIdealCotangentMap (I : Ideal R) :
    I.Cotangent →ₗ[R] (I.map (algebraMap R S)).Cotangent :=
  Ideal.mapCotangent I (I.map (algebraMap R S)) (Algebra.ofId R S) Ideal.le_comap_map

theorem extendedIdealCotangentMap_toCotangent (I : Ideal R) (x : I) :
    extendedIdealCotangentMap (S := S) I (I.toCotangent x) =
      (I.map (algebraMap R S)).toCotangent ⟨algebraMap R S x.val, Ideal.mem_map_of_mem _ x.property⟩ := rfl

theorem extendedIdealCotangentMap_isBaseChange [Module.Flat R S] (I : Ideal R) :
    IsBaseChange S (extendedIdealCotangentMap (S := S) I) := by
  apply IsBaseChange.of_equiv (FlatCotangentBaseChange.Construction.flatIdealCotangentEquiv R S I)
  intro x
  obtain ⟨x, rfl⟩ := I.toCotangent_surjective x
  rw [FlatCotangentBaseChange.Construction.flatIdealCotangentEquiv_tmul, one_smul, extendedIdealCotangentMap_toCotangent]

theorem extendedIdealCotangentMap_isLocalizedModule
    (M : Submonoid R) [IsLocalization M S] (I : Ideal R) :
    IsLocalizedModule M (extendedIdealCotangentMap (S := S) I) := by
  let : Module.Flat R S := IsLocalization.flat S M
  apply (isLocalizedModule_iff_isBaseChange M S _).mpr
  exact extendedIdealCotangentMap_isBaseChange I

end

end OAI.AlgebraicGeometry.Resolution.Blowups.LocalizedCotangentMap.Construction

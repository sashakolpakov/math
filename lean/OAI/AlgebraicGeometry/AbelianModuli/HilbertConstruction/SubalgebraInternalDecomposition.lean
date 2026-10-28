import Mathlib.Algebra.DirectSum.Decomposition
import Mathlib.Algebra.DirectSum.Module
import Mathlib.Algebra.Algebra.Subalgebra.Basic

/-! # Subalgebra Internal Decomposition -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.SubalgebraInternalDecomposition

noncomputable section

/-! Independent ambient submodules whose supremum is a subalgebra
give an actual internal decomposition of that subalgebra. -/
open scoped Classical
universe u v
variable {R A : Type u} [CommRing R] [CommRing A] [Algebra R A]
variable {ι : Type v}

theorem subalgebra_internalDecomposition (S : Subalgebra R A)
    (d : ι → Submodule R A) (hd : ∀ i, d i ≤ S.toSubmodule)
    (hi : iSupIndep d) (hs : iSup d = S.toSubmodule) :
    DirectSum.IsInternal (fun i => (d i).comap S.toSubmodule.subtype) := by
  apply DirectSum.isInternal_submodule_of_iSupIndep_of_iSup_eq_top
  · let e : Submodule R S ≃o Set.Iic S.toSubmodule := S.toSubmodule.mapIic
    have he : e ∘ (fun i => (d i).comap S.toSubmodule.subtype) =
        fun i => ⟨d i, hd i⟩ := by
      ext i x
      change x ∈ ((d i).comap S.toSubmodule.subtype).map S.toSubmodule.subtype ↔ x ∈ d i
      rw [Submodule.map_comap_subtype, inf_of_le_right (hd i)]
    rw [← iSupIndep_map_orderIso_iff e, he]
    exact iSupIndep.of_coe_Iic_comp (t := fun i => ⟨d i, hd i⟩) hi
  · apply Submodule.map_injective_of_injective (f := S.toSubmodule.subtype) Subtype.val_injective
    rw [Submodule.map_iSup, Submodule.map_top, Submodule.range_subtype]
    simp_rw [Submodule.map_comap_subtype, inf_of_le_right (hd _)]
    exact hs

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.SubalgebraInternalDecomposition

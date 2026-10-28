import OAI.AlgebraicGeometry.Crystalline.Cohomology.Cech.Cover
import Mathlib.Topology.Sheaves.SheafCondition.UniqueGluing

/-! # Sheaf Locality Is -/

namespace OAI.AlgebraicGeometry.Crystalline.Cohomology.SheafLocalityIs.SheafLocality

noncomputable section

/-!
# Detecting zero module sheaves on an open cover

Vanishing after restriction to every member of an open cover implies
vanishing globally. The proof uses the uniqueness clause in the actual
sheaf condition.
-/

open _root_.CategoryTheory Limits Opposite _root_.AlgebraicGeometry

universe u

variable (R : Type u) [CommRing R] (X : Scheme.{u})
  {ι : Type u} (U : ι → X.Opens) (hU : iSup U = ⊤)
  (H : Sheaf (Opens.grothendieckTopology X) (ModuleCat.{u} R))
  (hH : ∀ i, IsZero ((Cech.Cover.CechRestriction.sheafRestrictionFunctor R (U i).ι).obj H))

include hH in
theorem intersection_sections_isZero (i : ι) (V : X.Opens) : IsZero (H.obj.obj (op (V ⊓ U i))) := by
  have hz := Functor.map_isZero (sheafToPresheaf (Opens.grothendieckTopology (U i).toScheme)
    (ModuleCat.{u} R)) (hH i)
  have he := hz.obj (op ((U i).ι ⁻¹ᵁ V))
  have hV : (U i).ι ''ᵁ ((U i).ι ⁻¹ᵁ V) = V ⊓ U i := by
    rw [Scheme.Hom.image_preimage_eq_opensRange_inf, Scheme.Opens.opensRange_ι, inf_comm]
  change IsZero (H.obj.obj (op ((U i).ι ''ᵁ ((U i).ι ⁻¹ᵁ V)))) at he
  rw [hV] at he
  exact he

include hU hH in
/-- A module sheaf vanishes if its restrictions to an open cover vanish. -/
theorem isZero_of_restrictions : IsZero H := by
  apply IsZero.of_full_of_faithful_of_isZero (sheafToPresheaf (Opens.grothendieckTopology X)
    (ModuleCat.{u} R)) H
  apply Functor.isZero
  intro V
  apply ModuleCat.isZero_iff_subsingleton.mpr
  refine ⟨fun s t => ?_⟩
  have hcover : V.unop ≤ iSup (fun i => V.unop ⊓ U i) := by
    rw [← inf_iSup_eq, hU, inf_top_eq]
  apply TopCat.Sheaf.eq_of_locally_eq' H (fun i => V.unop ⊓ U i) V.unop
    (fun _ => homOfLE inf_le_left) hcover s t
  intro i
  have hz := intersection_sections_isZero R X U H hH i V.unop
  have hs := ModuleCat.isZero_iff_subsingleton.mp hz
  exact hs.elim _ _

end

end OAI.AlgebraicGeometry.Crystalline.Cohomology.SheafLocalityIs.SheafLocality

import Mathlib.AlgebraicGeometry.Restrict

/-! # Commuting Open Maps -/

namespace OAI.RepresentationTheory.Theta.Geometric.CommutingOpenMaps

noncomputable section

/-! Restricting a commuting triangle to the same target open gives
an actual map of the two inverse-image open schemes. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

variable {X Y Z : Scheme} (f : X ⟶ Y) (p : Y ⟶ Z) (q : X ⟶ Z)
    (h : f ≫ p = q) (U : Z.Opens)

include h in
theorem commutingOpenMap_preimage : q ⁻¹ᵁ U = f ⁻¹ᵁ (p ⁻¹ᵁ U) := by
  rw [← h, Scheme.Hom.comp_preimage]

def commutingOpenMap : (q ⁻¹ᵁ U).toScheme ⟶ (p ⁻¹ᵁ U).toScheme :=
  f.resLE (p ⁻¹ᵁ U) (q ⁻¹ᵁ U) (commutingOpenMap_preimage f p q h U).le

theorem commutingOpenMap_ι : commutingOpenMap f p q h U ≫ (p ⁻¹ᵁ U).ι = (q ⁻¹ᵁ U).ι ≫ f :=
  Scheme.Hom.resLE_comp_ι _ _

theorem commutingOpenMap_projection : commutingOpenMap f p q h U ≫ p ∣_ U = q ∣_ U := by
  apply (cancel_mono U.ι).mp
  rw [Category.assoc, morphismRestrict_ι, ← Category.assoc, commutingOpenMap_ι,
    Category.assoc, h, morphismRestrict_ι]

theorem commutingOpenMap_isPullback :
    IsPullback (commutingOpenMap f p q h U) (q ⁻¹ᵁ U).ι (p ⁻¹ᵁ U).ι f := by
  have he := commutingOpenMap_preimage f p q h U
  have H (V : X.Opens) (he : V = f ⁻¹ᵁ (p ⁻¹ᵁ U)) :
      IsPullback (f.resLE (p ⁻¹ᵁ U) V he.le) V.ι (p ⁻¹ᵁ U).ι f := by
    subst V
    simpa only [Scheme.Hom.resLE_eq_morphismRestrict] using isPullback_morphismRestrict f (p ⁻¹ᵁ U)
  exact H _ he

end

end OAI.RepresentationTheory.Theta.Geometric.CommutingOpenMaps

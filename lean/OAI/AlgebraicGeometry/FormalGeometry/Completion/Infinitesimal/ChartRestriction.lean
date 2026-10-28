import OAI.AlgebraicGeometry.FormalGeometry.Completion.Affine.InfinitesimalSections

/-! # Chart Restriction -/

namespace OAI.AlgebraicGeometry.FormalGeometry.Completion.Infinitesimal.ChartRestriction.Construction

noncomputable section

/-! The actual infinitesimal chart quotient isomorphisms commute with restriction. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

variable {R : Type u} [CommRing R] (I : Ideal R)
  {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of R))

theorem baseOpenSectionsMap_restrict {U V : X.Opens} (h : V ≤ U) :
    (X.presheaf.map (homOfLE h).op).hom.comp (Affine.InfinitesimalSections.Construction.baseOpenSectionsMap f U) =
      Affine.InfinitesimalSections.Construction.baseOpenSectionsMap f V := by
  change (((Scheme.ΓSpecIso (.of R)).inv ≫ f.appLE ⊤ U (by simp)) ≫
    X.presheaf.map (homOfLE h).op).hom = _
  rw [Category.assoc, Scheme.Hom.appLE_map]
  rfl

/-- Restriction on the quotients of the original affine chart rings. -/
def infinitesimalChartQuotientRestriction (n : ℕ) {U V : X.Opens} (h : V ≤ U) :
    CommRingCat.of (Γ(X, U) ⧸ (I ^ (n + 1)).map (Affine.InfinitesimalSections.Construction.baseOpenSectionsMap f U)) ⟶
      CommRingCat.of (Γ(X, V) ⧸ (I ^ (n + 1)).map (Affine.InfinitesimalSections.Construction.baseOpenSectionsMap f V)) :=
  CommRingCat.ofHom (Ideal.quotientMap _ (X.presheaf.map (homOfLE h).op).hom (by
    rw [← Ideal.map_le_iff_le_comap, Ideal.map_map, baseOpenSectionsMap_restrict]))

/-- The quotient isomorphism is compatible with the literal sheaf restriction maps. -/
theorem affineInfinitesimalSectionsIso_restrict (n : ℕ) {U V : X.Opens}
    (hU : IsAffineOpen U) (hV : IsAffineOpen V) (h : V ≤ U) :
    (Affine.InfinitesimalSections.Construction.affineInfinitesimalSectionsIso I f n U hU).hom ≫
        (Neighborhoods.Construction.infinitesimalNeighborhood I f n).presheaf.map
          (homOfLE ((pullback.fst f (Neighborhoods.Construction.infinitesimalBaseToSpec I n)).preimage_mono h)).op =
      infinitesimalChartQuotientRestriction I f n h ≫
        (Affine.InfinitesimalSections.Construction.affineInfinitesimalSectionsIso I f n V hV).hom := by
  ext s
  change (Neighborhoods.Construction.infinitesimalNeighborhood I f n).presheaf.map _
    ((Affine.InfinitesimalSections.Construction.affineInfinitesimalSectionsIso I f n U hU).hom (Ideal.Quotient.mk _ s)) =
      (Affine.InfinitesimalSections.Construction.affineInfinitesimalSectionsIso I f n V hV).hom
        (Ideal.Quotient.mk _ (X.presheaf.map (homOfLE h).op s))
  rw [Affine.InfinitesimalSections.Construction.affineInfinitesimalSectionsIso_mk, Affine.InfinitesimalSections.Construction.affineInfinitesimalSectionsIso_mk]
  exact (ConcreteCategory.congr_hom
    ((pullback.fst f (Neighborhoods.Construction.infinitesimalBaseToSpec I n)).naturality (homOfLE h).op) s).symm

end

end OAI.AlgebraicGeometry.FormalGeometry.Completion.Infinitesimal.ChartRestriction.Construction

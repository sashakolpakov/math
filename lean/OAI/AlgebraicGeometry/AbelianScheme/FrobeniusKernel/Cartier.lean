import OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.CartierModel

/-! # Cartier -/

namespace OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel

noncomputable section

/-! The actual source group inherits finite local freeness from its coordinates. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry Opposite

universe u

variable {R : CommRingCat.{u}} {G : Grp (Over (Spec R))}

theorem Cartier.Construction.group_finiteLocallyFree_of_iso {G H : Grp (Over (Spec R))} (e : G ≅ H)
    (hH : IsFinite H.X.hom ∧ Flat H.X.hom ∧ LocallyOfFinitePresentation H.X.hom) :
    IsFinite G.X.hom ∧ Flat G.X.hom ∧ LocallyOfFinitePresentation G.X.hom := by
  have : IsFinite H.X.hom := hH.1
  have : Flat H.X.hom := hH.2.1
  have : LocallyOfFinitePresentation H.X.hom := hH.2.2
  let f : G.X.left ⟶ H.X.left := e.hom.hom.hom.left
  have : IsIso f := inferInstanceAs (IsIso (((Grp.forget (Over (Spec R))) ⋙ Over.forget _).map e.hom))
  have hw : f ≫ H.X.hom = G.X.hom := e.hom.hom.hom.w
  exact ⟨hw ▸ (inferInstance : IsFinite (f ≫ H.X.hom)),
    hw ▸ (inferInstance : Flat (f ≫ H.X.hom)),
    hw ▸ (inferInstance : LocallyOfFinitePresentation (f ≫ H.X.hom))⟩

theorem CartierModel.Construction.CartierCoordinates.group_finiteLocallyFree (P : CartierModel.Construction.CartierCoordinates R G) :
    IsFinite G.X.hom ∧ Flat G.X.hom ∧ LocallyOfFinitePresentation G.X.hom := by
  apply Cartier.Construction.group_finiteLocallyFree_of_iso P.comparison.symm
  exact (CartierDuality.FiniteLocallyFreeCoordinates.Construction.finiteLocallyFree_spec_iff R P.algebra).mpr ⟨P.finite, P.projective⟩

end

end OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel

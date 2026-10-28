import OAI.AlgebraicGeometry.Resolution.Blowups.Open.AffineBoundaryRestriction

/-! # Atlas Iso Transport -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups

noncomputable section

/-! Transport native labelled boundary atlases through specified actual scheme isomorphisms. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

def Global.MonomialBoundaryAtlas.Construction.GlobalMonomialBoundaryAtlas.transportIso
    {V X : Scheme} {g : V ⟶ Foundations.Scheme.ProjectiveSpace.complexBase} (f : X ⟶ Foundations.Scheme.ProjectiveSpace.complexBase)
    {β : Type} {E : β → V.IdealSheafData} (D : β → X.IdealSheafData) {L : List (Finset β)}
    (A : Global.MonomialBoundaryAtlas.Construction.GlobalMonomialBoundaryAtlas g E L) (e : V ≅ X)
    (hg : e.hom ≫ f = g) (hD : ∀ j, (D j).comap e.hom = E j) :
    Global.MonomialBoundaryAtlas.Construction.GlobalMonomialBoundaryAtlas f D L := by
  have hg' : e.inv ≫ g = f := by
    rw [← hg, ← Category.assoc, e.inv_hom_id, Category.id_comp]
  have hD' : (fun j => (E j).comap e.inv) = D := by
    funext j
    rw [← hD j, ← Scheme.IdealSheafData.comap_comp, e.inv_hom_id, Scheme.IdealSheafData.comap_id]
  have B := A.comapOpen g e.inv
  rw [hg', hD'] at B
  exact B

end

end OAI.AlgebraicGeometry.Resolution.Blowups

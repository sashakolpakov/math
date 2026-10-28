import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Embedded.IsomorphismUniqueness

/-! # Isomorphism Transport Equivalence -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Moduli

noncomputable section

/-! Transport through fixed complete moduli isomorphisms is an equivalence on isomorphism sets. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

def Isomorphisms.LevelPreservingIso.transportEquiv {S : Scheme.{u}} {g N : ℕ} {δ : Fin g → ℕ}
    {A A' B B' : PolarizationData.PolarizedAbelianWithFullLevel g δ N S}
    (a : Isomorphisms.LevelPreservingIso A A') (b : Isomorphisms.LevelPreservingIso B B') :
    Isomorphisms.LevelPreservingIso A B ≃ Isomorphisms.LevelPreservingIso A' B' where
  toFun e := (a.symm.trans e).trans b
  invFun e := (a.trans e).trans b.symm
  left_inv e := by
    apply Isomorphisms.LevelPreservingIso.ext_abelian
    change (a.abelian.hom ≫ ((a.abelian.inv ≫ e.abelian.hom) ≫ b.abelian.hom)) ≫ b.abelian.inv = e.abelian.hom
    simp only [Category.assoc, Iso.hom_inv_id_assoc, Iso.hom_inv_id, Category.comp_id]
  right_inv e := by
    apply Isomorphisms.LevelPreservingIso.ext_abelian
    change (a.abelian.inv ≫ ((a.abelian.hom ≫ e.abelian.hom) ≫ b.abelian.inv)) ≫ b.abelian.hom = e.abelian.hom
    simp only [Category.assoc, Iso.inv_hom_id_assoc, Iso.inv_hom_id, Category.comp_id]

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Moduli

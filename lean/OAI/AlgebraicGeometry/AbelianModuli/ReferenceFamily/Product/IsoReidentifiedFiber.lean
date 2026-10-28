import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.NormalizedDual.OpenProductData

/-! # Iso Reidentified Fiber -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Product.IsoReidentifiedFiber

/-! An isomorphism to any constant product can be rewritten as an
actual normalized product with its own special fiber. -/

open _root_.CategoryTheory

variable {C D : Type*} [Category* C] [Category* D]
    (F : C ⥤ D) (G : D ⥤ C) (n : F ⋙ G ≅ 𝟭 C) (X : D) (A : C) (e : X ≅ F.obj A)

def productIsoReducedIso : G.obj X ≅ A := G.mapIso e ≪≫ n.app A

def productIsoCanonicalFiber : X ≅ F.obj (G.obj X) :=
  e ≪≫ F.mapIso (productIsoReducedIso F G n X A e).symm

theorem productIsoCanonicalFiber_normalized : NormalizedDual.OpenProductData.NormalizesProductFiber F G n (productIsoCanonicalFiber F G n X A e) := by
  let b := productIsoReducedIso F G n X A e
  have hn : G.map (F.map b.inv) ≫ n.hom.app (G.obj X) = n.hom.app A ≫ b.inv := n.hom.naturality b.inv
  change G.map (e.hom ≫ F.map b.inv) ≫ n.hom.app (G.obj X) = 𝟙 (G.obj X)
  rw [Functor.map_comp, Category.assoc, hn]
  exact (Category.assoc _ _ _).symm.trans b.hom_inv_id

theorem productIsoCanonicalFiber_recovery :
    (productIsoCanonicalFiber F G n X A e).hom ≫ F.map (productIsoReducedIso F G n X A e).hom = e.hom := by
  let b := productIsoReducedIso F G n X A e
  change (e.hom ≫ F.map b.inv) ≫ F.map b.hom = e.hom
  rw [Category.assoc, ← Functor.map_comp, Iso.inv_hom_id, F.map_id, Category.comp_id]

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Product.IsoReidentifiedFiber

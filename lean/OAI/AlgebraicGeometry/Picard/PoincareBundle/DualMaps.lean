import OAI.AlgebraicGeometry.Picard.PoincareBundle.Homogeneous

/-! # Dual Maps -/

namespace OAI.AlgebraicGeometry.Picard.PoincareBundle.DualMaps

noncomputable section

/-!
# Morphisms induced on represented dual Picard functors for PoincareBundle

The representatives below satisfy the usual homogeneous-Picard universal
property. No quotient or polarization descent assertion is assumed.
The induced morphisms are constructed from geometric pullback.
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry Opposite
open scoped _root_.CategoryTheory.MonObj

universe u

open OAI.AlgebraicGeometry.Picard.PoincareBundle.Homogeneous

variable {S : Scheme.{u}} {A B C Adual Bdual Cdual : Over S}
  [GrpObj A] [GrpObj B] [GrpObj C]
  (DA : (Homogeneous.homogeneousSheaf A).obj.RepresentableBy Adual)
  (DB : (Homogeneous.homogeneousSheaf B).obj.RepresentableBy Bdual)
  (DC : (Homogeneous.homogeneousSheaf C).obj.RepresentableBy Cdual)

/-- The contravariant morphism induced by pullback on homogeneous line classes. -/
def representedDualMap (f : A ⟶ B) [IsMonHom f] : Bdual ⟶ Adual :=
  DA.homEquiv.symm ((Homogeneous.pullbackHomogeneousSheaf f).hom.app (op Bdual)
    (DB.homEquiv (𝟙 Bdual)))

/-- The constructed morphism acts on every test scheme by actual Picard pullback. -/
theorem representedDualMap_action (f : A ⟶ B) [IsMonHom f]
    {T : Over S} (x : T ⟶ Bdual) :
    DA.homEquiv (x ≫ representedDualMap DA DB f) =
      (Homogeneous.pullbackHomogeneousSheaf f).hom.app (op T) (DB.homEquiv x) := by
  rw [DA.homEquiv_comp]
  dsimp only [representedDualMap]
  rw [Equiv.apply_symm_apply]
  rw [← (Homogeneous.pullbackHomogeneousSheaf f).hom.naturality_apply x.op]
  rw [← DB.homEquiv_comp x (𝟙 Bdual), Category.comp_id]

/-- The Picard pullback property determines the represented dual morphism. -/
theorem representedDualMap_unique (f : A ⟶ B) [IsMonHom f] (d : Bdual ⟶ Adual)
    (hd : ∀ (T : Over S) (x : T ⟶ Bdual),
      DA.homEquiv (x ≫ d) =
        (Homogeneous.pullbackHomogeneousSheaf f).hom.app (op T) (DB.homEquiv x)) :
    d = representedDualMap DA DB f := by
  apply DA.homEquiv.injective
  simpa only [Category.id_comp] using
    (hd Bdual (𝟙 Bdual)).trans (representedDualMap_action DA DB f (𝟙 Bdual)).symm

@[simp]
theorem representedDualMap_id : representedDualMap DA DA (𝟙 A) = 𝟙 Adual := by
  apply DA.homEquiv.injective
  dsimp only [representedDualMap]
  rw [Equiv.apply_symm_apply, Homogeneous.pullbackHomogeneousSheaf_id]
  rfl

/-- Dual maps reverse composition because geometric Picard pullback does. -/
theorem representedDualMap_comp (f : A ⟶ B) (g : B ⟶ C) [IsMonHom f] [IsMonHom g] :
    representedDualMap DA DC (f ≫ g) =
      representedDualMap DB DC g ≫ representedDualMap DA DB f := by
  symm
  apply representedDualMap_unique DA DC (f ≫ g)
  intro T x
  rw [← Category.assoc, representedDualMap_action, representedDualMap_action]
  exact (congrArg (fun b => b.hom.app (op T) (DC.homEquiv x))
    (Homogeneous.pullbackHomogeneousSheaf_comp f g)).symm

/-- A group-scheme isomorphism induces an isomorphism of the represented duals. -/
def representedDualIso (e : A ≅ B) [IsMonHom e.hom] : Bdual ≅ Adual where
  hom := representedDualMap DA DB e.hom
  inv := representedDualMap DB DA e.inv
  hom_inv_id := by
    rw [← representedDualMap_comp DB DA DB e.inv e.hom]
    simp only [e.inv_hom_id, representedDualMap_id]
  inv_hom_id := by
    rw [← representedDualMap_comp DA DB DA e.hom e.inv]
    simp only [e.hom_inv_id, representedDualMap_id]

end

end OAI.AlgebraicGeometry.Picard.PoincareBundle.DualMaps

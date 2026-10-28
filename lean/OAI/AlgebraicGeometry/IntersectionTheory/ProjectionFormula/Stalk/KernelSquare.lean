import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Generic.StalkSquare

/-! # Kernel Square -/

namespace OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Stalk.KernelSquare

noncomputable section

/-! Kernels of actual stalk maps transport through an open chart
square, including the point identification supplied by the square. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open _root_.CategoryTheory _root_.AlgebraicGeometry

variable {V W Y X : Scheme} (j : Y ⟶ X) (i : W ⟶ X) (k : V ⟶ W) (l : V ⟶ Y)
  (h : l ≫ j = k ≫ i) (v : V)

def map : X.presheaf.stalk (j (l v)) ⟶ W.presheaf.stalk (k v) :=
  eqToHom (congrArg (fun x => X.presheaf.stalk x)
    (congrArg (fun g : V ⟶ X => g v) h)) ≫ i.stalkMap (k v)

theorem square : KernelSquare.map j i k l h v ≫ k.stalkMap v = j.stalkMap (l v) ≫ l.stalkMap v := by
  rw [KernelSquare.map, Category.assoc, ← Scheme.Hom.stalkMap_comp]
  exact (Generic.StalkSquare.stalkMap_congr h.symm v).trans
    (Scheme.Hom.stalkMap_comp l j v)

theorem kernel_comap [IsIso (k.stalkMap v)] :
    RingHom.ker (KernelSquare.map j i k l h v).hom =
      (RingHom.ker (l.stalkMap v).hom).comap (j.stalkMap (l v)).hom := by
  ext a
  change KernelSquare.map j i k l h v a = 0 ↔ l.stalkMap v (j.stalkMap (l v) a) = 0
  have he := congrArg (fun g : X.presheaf.stalk (j (l v)) ⟶ V.presheaf.stalk v => g a)
    (square j i k l h v)
  exact ((map_eq_zero_iff (k.stalkMap v).hom
    (ConcreteCategory.bijective_of_isIso (k.stalkMap v)).injective).symm).trans
      (iff_of_eq (congrArg (· = 0) he))

theorem principal [IsIso (k.stalkMap v)] [IsIso (j.stalkMap (l v))]
    (r : X.presheaf.stalk (j (l v)))
    (hr : RingHom.ker (l.stalkMap v).hom = Ideal.span {j.stalkMap (l v) r}) :
    RingHom.ker (KernelSquare.map j i k l h v).hom = Ideal.span {r} := by
  rw [kernel_comap, hr]
  have hm : (Ideal.span {r}).map (j.stalkMap (l v)).hom =
      Ideal.span {j.stalkMap (l v) r} := by rw [Ideal.map_span, Set.image_singleton]
  rw [← hm]
  exact Ideal.comap_map_of_bijective _
    (ConcreteCategory.bijective_of_isIso (j.stalkMap (l v)))

theorem kernel_map [IsIso (k.stalkMap v)] [IsIso (j.stalkMap (l v))] :
    RingHom.ker (l.stalkMap v).hom =
      (RingHom.ker (KernelSquare.map j i k l h v).hom).map (j.stalkMap (l v)).hom := by
  rw [kernel_comap]
  exact (Ideal.map_comap_of_surjective _
    (ConcreteCategory.bijective_of_isIso (j.stalkMap (l v))).surjective _).symm

include h in
theorem principal_to_chart [IsIso (k.stalkMap v)] [IsIso (j.stalkMap (l v))]
    (r : ∀ x : X, X.presheaf.stalk x)
    (hr : RingHom.ker (i.stalkMap (k v)).hom = Ideal.span {r (i (k v))}) :
    RingHom.ker (l.stalkMap v).hom = Ideal.span {j.stalkMap (l v) (r (j (l v)))} := by
  have add_transport (x x' : X) (hp : x = x') (S : CommRingCat)
      (β : X.presheaf.stalk x' ⟶ S) (hb : RingHom.ker β.hom = Ideal.span {r x'}) :
      RingHom.ker (eqToHom (congrArg (fun z => X.presheaf.stalk z) hp) ≫ β).hom =
        Ideal.span {r x} := by
    subst x'
    simpa only [eqToHom_refl, Category.id_comp] using hb
  have hb := add_transport (j (l v)) (i (k v))
    (congrArg (fun g : V ⟶ X => g v) h) _ (i.stalkMap (k v)) hr
  rw [kernel_map j i k l h v]
  change (RingHom.ker (eqToHom _ ≫ i.stalkMap (k v)).hom).map _ = _
  rw [hb, Ideal.map_span, Set.image_singleton]

include h in
theorem principal_at_image [IsIso (k.stalkMap v)] [IsIso (j.stalkMap (l v))]
    (r : ∀ x : X, X.presheaf.stalk x)
    (hr : RingHom.ker (l.stalkMap v).hom = Ideal.span {j.stalkMap (l v) (r (j (l v)))}) :
    RingHom.ker (i.stalkMap (k v)).hom = Ideal.span {r (i (k v))} := by
  have remove_transport (x x' : X) (hp : x = x') (S : CommRingCat)
      (β : X.presheaf.stalk x' ⟶ S)
      (hb : RingHom.ker (eqToHom (congrArg (fun z => X.presheaf.stalk z) hp) ≫ β).hom =
        Ideal.span {r x}) : RingHom.ker β.hom = Ideal.span {r x'} := by
    subst x'
    simpa only [eqToHom_refl, Category.id_comp] using hb
  exact remove_transport (j (l v)) (i (k v))
    (congrArg (fun g : V ⟶ X => g v) h) _ (i.stalkMap (k v))
    (principal j i k l h v (r (j (l v))) hr)

end

end OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Stalk.KernelSquare

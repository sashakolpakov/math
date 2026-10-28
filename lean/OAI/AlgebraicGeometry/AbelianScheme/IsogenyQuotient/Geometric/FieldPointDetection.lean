import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Field.PointGroupDetection

/-! # Field Point Detection -/

namespace OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Geometric.FieldPointDetection.Construction

noncomputable section

/-! Equality after geometric base change determines the value of a
map on every field-valued point, by faithfully flat scalar extension. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.CategoryTheory.Limits

universe u

set_option backward.isDefEq.respectTransparency false in
theorem overHom_fieldPoint_eq_of_baseChange
    {S : Scheme.{u}} {X Y : Over S} (f g : X ⟶ Y)
    {K : Type u} [Field K] (s : Spec (.of K) ⟶ S)
    (h : (Over.pullback s).map f = (Over.pullback s).map g) (x : Over.mk s ⟶ X) : x ≫ f = x ≫ g := by
  let l : Spec (.of K) ⟶ pullback X.hom s :=
    pullback.lift x.left (𝟙 _) (by rw [Category.id_comp]; exact Over.w x)
  have H := congrArg (fun z => l ≫ z.left ≫ pullback.fst Y.hom s) h
  apply Over.OverMorphism.ext
  change x.left ≫ f.left = x.left ≫ g.left
  simpa only [Over.pullback_map_left, ← Category.assoc, l, pullback.lift_fst] using H

set_option backward.isDefEq.respectTransparency false in
theorem overHom_fieldPoint_eq_of_geometric_baseChanges
    {S : Scheme.{u}} {X Y : Over S} (f g : X ⟶ Y)
    (h : ∀ (K : Type u) [Field K] [IsAlgClosed K] (s : Spec (.of K) ⟶ S),
      (Over.pullback s).map f = (Over.pullback s).map g)
    {K : Type u} [Field K] (s : Spec (.of K) ⟶ S) (x : Over.mk s ⟶ X) : x ≫ f = x ≫ g := by
  let a := Spec.map (CommRingCat.ofHom (algebraMap K (AlgebraicClosure K)))
  have : Flat a := inferInstanceAs
    (Flat (Spec.map (CommRingCat.ofHom (algebraMap K (AlgebraicClosure K)))))
  have : Surjective a := ⟨Function.surjective_to_subsingleton _⟩
  have : QuasiCompact a := inferInstanceAs
    (QuasiCompact (Spec.map (CommRingCat.ofHom (algebraMap K (AlgebraicClosure K)))))
  let z : Over.mk (a ≫ s) ⟶ Over.mk s := Over.homMk a rfl
  have : Epi z.left := inferInstanceAs (Epi a)
  have : Epi z := Over.epi_of_epi_left z
  apply (cancel_epi z).mp
  simpa only [Category.assoc] using
    overHom_fieldPoint_eq_of_baseChange f g (a ≫ s) (h (AlgebraicClosure K) (a ≫ s)) (z ≫ x)

end

end OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Geometric.FieldPointDetection.Construction

import OAI.AlgebraicGeometry.SheafCohomology.Cech.Cochains

/-! # Additive Cech Cover Congr -/

namespace OAI.AlgebraicGeometry.Comparison.Betti.AdditiveCechCoverCongr

noncomputable section

section

/-! Every projection of the original additive Čech cosimplicial map is the
original presheaf restriction attached to that tuple. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.TopologicalSpace Opposite
open scoped Simplicial

variable {X ι : Type} [TopologicalSpace X]
  (F : (Opens X)ᵒᵖ ⥤ AddCommGrpCat.{0}) (U : ι → Opens X)

theorem additiveCechMap_proj {n m : SimplexCategory} (f : n ⟶ m)
    (a : Fin (m.len + 1) → ι) :
    (((FormalCoproduct.cosimplicialObjectFunctor (FormalCoproduct.mk _ U).cech).obj F).map f) ≫
        Pi.π (fun b : Fin (m.len + 1) → ι => F.obj (op (∏ᶜ fun k => U (b k)))) a =
      Pi.π (fun b : Fin (n.len + 1) → ι => F.obj (op (∏ᶜ fun k => U (b k))))
          (a ∘ f.toOrderHom) ≫
        F.map (((FormalCoproduct.mk _ U).mapPower f.toOrderHom).φ a).op := by
  rw [FormalCoproduct.cosimplicialObjectFunctor_obj_map, FormalCoproduct.cech_map]
  exact Pi.lift_comp_π _ a

end

/-! Equality of cover opens gives the original restriction isomorphism on each native Čech factor. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.TopologicalSpace Opposite

variable {X : Type} [TopologicalSpace X] {ι : Type}
    (F : (Opens X)ᵒᵖ ⥤ AddCommGrpCat.{0}) {U V : ι → Opens X}

def additiveCechCoverCongrIso (h : U = V) :
    (cechComplexFunctor U).obj F ≅ (cechComplexFunctor V).obj F :=
  eqToIso (congrArg (fun W => (cechComplexFunctor W).obj F) h)

theorem additiveCechCoverCongrIso_hom_proj (h : U = V) (q : ℕ) (t : Fin (q + 1) → ι) :
    (additiveCechCoverCongrIso F h).hom.f q ≫
        Pi.π (fun a : Fin (q + 1) → ι => F.obj (op (∏ᶜ fun k => V (a k)))) t =
      Pi.π (fun a : Fin (q + 1) → ι => F.obj (op (∏ᶜ fun k => U (a k)))) t ≫
        F.map (eqToHom (congrArg op (congrArg (fun W : ι → Opens X => ∏ᶜ fun k => W (t k)) h))) := by
  subst V
  change 𝟙 _ ≫ _ = _ ≫ F.map (𝟙 _)
  let p := Pi.π (fun a : Fin (q + 1) → ι => F.obj (op (∏ᶜ fun k => U (a k)))) t
  exact (Category.id_comp p).trans ((Category.comp_id p).symm.trans
    (congrArg (p ≫ ·) (F.map_id _).symm))

end

end OAI.AlgebraicGeometry.Comparison.Betti.AdditiveCechCoverCongr

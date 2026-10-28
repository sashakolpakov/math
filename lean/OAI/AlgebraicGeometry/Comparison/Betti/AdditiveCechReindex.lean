import OAI.AlgebraicGeometry.Comparison.Betti.AdditiveCechCoverCongr

/-! # Additive Cech Reindex -/

namespace OAI.AlgebraicGeometry.Comparison.Betti.AdditiveCechReindex

noncomputable section

/-! Relabeling a cover preserves the original Cech complex and its intersection projections. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.TopologicalSpace Opposite

universe u v w w'

def cechRightOpIso {C : Type u} {D : Type v} [Category.{w} C] [Category.{w'} D]
    {F G : Cᵒᵖ ⥤ D} (e : F ≅ G) :
    G.rightOp ≅ F.rightOp where
  hom := e.hom.rightOp
  inv := e.inv.rightOp
  hom_inv_id := by rw [← NatTrans.rightOp_comp, e.inv_hom_id, NatTrans.rightOp_id]
  inv_hom_id := by rw [← NatTrans.rightOp_comp, e.hom_inv_id, NatTrans.rightOp_id]

variable {X : Type} [TopologicalSpace X] {ι κ : Type}
    (F : (Opens X)ᵒᵖ ⥤ AddCommGrpCat.{0}) (U : ι → Opens X) (e : κ ≃ ι)

def additiveCoverReindexIso :
    FormalCoproduct.mk κ (U ∘ e) ≅ FormalCoproduct.mk ι U :=
  FormalCoproduct.isoOfComponents e (fun _ => Iso.refl _)

def additiveCechReindexIso : (cechComplexFunctor U).obj F ≅ (cechComplexFunctor (U ∘ e)).obj F :=
  (AlgebraicTopology.alternatingCofaceMapComplex AddCommGrpCat).mapIso
    (Functor.isoWhiskerRight
      (cechRightOpIso (FormalCoproduct.cechFunctor.mapIso (additiveCoverReindexIso U e)))
      ((FormalCoproduct.evalOp (Opens X) AddCommGrpCat).obj F))

theorem additiveCechReindexIso_hom_proj (q : ℕ) (t : Fin (q + 1) → κ) :
    (additiveCechReindexIso F U e).hom.f q ≫
      Pi.π (fun a : Fin (q + 1) → κ => F.obj (op (∏ᶜ fun k => U (e (a k))))) t =
      Pi.π (fun a : Fin (q + 1) → ι => F.obj (op (∏ᶜ fun k => U (a k)))) (e ∘ t) := by
  let P := fun a : Fin (q + 1) → ι => F.obj (op (∏ᶜ fun k => U (a k)))
  change (Pi.lift (fun a : Fin (q + 1) → κ =>
      Pi.π P (e ∘ a) ≫ F.map ((CategoryTheory.Limits.Pi.map
        (fun k : Fin (q + 1) => 𝟙 (U (e (a k))))).op))) ≫ _ = _
  rw [Pi.lift_comp_π]
  have h : CategoryTheory.Limits.Pi.map (fun k : Fin (q + 1) => 𝟙 (U (e (t k)))) = 𝟙 _ :=
    Subsingleton.elim _ _
  rw [h, op_id]
  exact (congrArg (Pi.π P (e ∘ t) ≫ ·)
    (F.map_id (op (∏ᶜ fun k => U (e (t k)))))).trans (Category.comp_id _)

end

end OAI.AlgebraicGeometry.Comparison.Betti.AdditiveCechReindex

import OAI.AlgebraicGeometry.Picard.PoincareBundle.Kernel.PairDetectsMorphisms
import OAI.AlgebraicGeometry.Picard.PoincareBundle.PullbackFiberComposition

/-! # Fiber Transport -/

namespace OAI.AlgebraicGeometry.Picard.PoincareBundle.Recovered.FiberTransport

noncomputable section

/-!
# Recovery on every test fiber identifies the actual descent transport
-/

open _root_.CategoryTheory _root_.CategoryTheory.Limits Opposite

universe u v u' v'

variable {C : Type u} [Category.{v} C] [HasPullbacks C]
  (F : Pseudofunctor (LocallyDiscrete Cᵒᵖ) Cat.{v', u'}) {X Y : C} (f : X ⟶ Y)
  (D : F.DescentData (fun (_ : PUnit.{1}) => f)) (P : F.obj (.mk (op Y)))
  (e : (F.map f.op.toLoc).toFunctor.obj P ≅ D.obj PUnit.unit)

/-- The canonical fiber recovery combines composition of pullback with the specified source recovery. -/
def recoveryIso {T : C} (x : T ⟶ X) (q : T ⟶ Y) (hx : x ≫ f = q) :
    (F.map q.op.toLoc).toFunctor.obj P ≅ (F.map x.op.toLoc).toFunctor.obj (D.obj PUnit.unit) :=
  (PullbackFiberComposition.fiberIsoTo F f P x q hx).symm ≪≫ (F.map x.op.toLoc).toFunctor.mapIso e

variable (ha : (F.map (pullback.fst f f).op.toLoc).toFunctor.map e.hom ≫
    D.hom (pullback.snd f f ≫ f) (i₁ := PUnit.unit) (i₂ := PUnit.unit)
      (pullback.fst f f) (pullback.snd f f) pullback.condition rfl =
  (Pseudofunctor.DescentData.ofObj (F := F) (f := fun (_ : PUnit.{1}) => f) P).hom
      (pullback.snd f f ≫ f) (i₁ := PUnit.unit) (i₂ := PUnit.unit)
      (pullback.fst f f) (pullback.snd f f) pullback.condition rfl ≫
    (F.map (pullback.snd f f).op.toLoc).toFunctor.map e.hom)

include ha in
/-- The canonical recovered fibers respect the original transport on every equal-image pair. -/
theorem recovery_hom {T : C} (q : T ⟶ Y) (x y : T ⟶ X) (hx : x ≫ f = q) (hy : y ≫ f = q) :
    (recoveryIso F f D P e x q hx).hom ≫ D.hom q (i₁ := PUnit.unit) (i₂ := PUnit.unit) x y hx hy =
      (recoveryIso F f D P e y q hy).hom := by
  let cx := PullbackFiberComposition.fiberIsoTo F f P x q hx
  let cy := PullbackFiberComposition.fiberIsoTo F f P y q hy
  have h := Kernel.PairDetectsMorphisms.compatible F f
    (Pseudofunctor.DescentData.ofObj (F := F) (f := fun (_ : PUnit.{1}) => f) P) D e.hom ha q x y hx hy
  change (F.map x.op.toLoc).toFunctor.map e.hom ≫ D.hom q x y hx hy =
    (cx.hom ≫ cy.inv) ≫ (F.map y.op.toLoc).toFunctor.map e.hom at h
  change (cx.inv ≫ (F.map x.op.toLoc).toFunctor.map e.hom) ≫ D.hom q x y hx hy =
    cy.inv ≫ (F.map y.op.toLoc).toFunctor.map e.hom
  rw [Category.assoc, h]
  simp only [Category.assoc, Iso.inv_hom_id_assoc]

include ha in
/-- The original full descent morphism is exactly change between the two canonical recovered fibers. -/
theorem transport_eq {T : C} (q : T ⟶ Y) (x y : T ⟶ X) (hx : x ≫ f = q) (hy : y ≫ f = q) :
    D.hom q (i₁ := PUnit.unit) (i₂ := PUnit.unit) x y hx hy =
      (recoveryIso F f D P e x q hx).inv ≫ (recoveryIso F f D P e y q hy).hom := by
  apply (cancel_epi (recoveryIso F f D P e x q hx).hom).mp
  rw [recovery_hom F f D P e ha, ← Category.assoc, Iso.hom_inv_id, Category.id_comp]

end

end OAI.AlgebraicGeometry.Picard.PoincareBundle.Recovered.FiberTransport

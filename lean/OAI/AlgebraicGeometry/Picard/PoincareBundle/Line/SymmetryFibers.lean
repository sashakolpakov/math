import OAI.AlgebraicGeometry.Picard.PoincareBundle.GlobalFrameNaturality
import OAI.AlgebraicGeometry.Picard.PoincareBundle.Line.FiberIsomorphisms

/-! # Symmetry Fibers -/

namespace OAI.AlgebraicGeometry.Picard.PoincareBundle.Line.SymmetryFibers

noncomputable section

/-! A global line symmetry induces natural isomorphisms between the corresponding actual test fibers. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

open OAI.AlgebraicGeometry.Picard.PoincareBundle.Line.Fibers OAI.AlgebraicGeometry.Picard.PoincareBundle.GlobalPullbackFrame OAI.AlgebraicGeometry.Picard.PoincareBundle.GlobalFrameNaturality

theorem inverse_square {C : Type*} [Category C] {A B D E : C}
    (a : A ≅ B) (b : D ≅ E) (c : A ≅ D) (d : B ≅ E) (h : a ≪≫ d = c ≪≫ b) :
    a.symm ≪≫ c = d ≪≫ b.symm := by
  have hh := congrArg (fun r => a.symm ≪≫ r ≪≫ b.symm) h
  simpa only [Iso.trans_assoc, Iso.symm_self_id_assoc, Iso.self_symm_id, Iso.trans_refl] using hh.symm

theorem inverse_functor_square {C D : Type*} [Category C] [Category D]
    (F : C ⥤ D) {A B E : C} {A' B' E' : D}
    (c : A ≅ B) (s : A ≅ E) (c' : A' ≅ B') (s' : A' ≅ E')
    (u : F.obj A ≅ A') (v : F.obj B ≅ B') (w : F.obj E ≅ E')
    (hc : F.mapIso c ≪≫ v = u ≪≫ c') (hs : F.mapIso s ≪≫ w = u ≪≫ s') :
    F.mapIso (c.symm ≪≫ s) ≪≫ w = v ≪≫ c'.symm ≪≫ s' := by
  have he := inverse_square (F.mapIso c) c' u v hc
  rw [Functor.mapIso_trans, Functor.mapIso_symm, Iso.trans_assoc, hs,
    ← Iso.trans_assoc, he, Iso.trans_assoc]

variable {S : Scheme.{u}} {E : Over S} (L : Bundles.LineBundle E.left)
  (g : E ⟶ E) (σ : (Scheme.Modules.pullback g.left).obj L.sheaf ≅ L.sheaf)

/-- Evaluate a global line symmetry at an arbitrary scheme-valued point. -/
def atPoint {T : Over S} (q : T ⟶ E) : Fibers.fiber L (q ≫ g) ≅ Fibers.fiber L q :=
  (GlobalPullbackFrame.comparison g L q (q ≫ g) rfl).symm ≪≫ (Scheme.Modules.pullback q.left).mapIso σ

theorem atPoint_eq {T : Over S} (q : T ⟶ E) :
    atPoint L g σ q = ((Scheme.Modules.pullbackComp q.left g.left).app L.sheaf).symm ≪≫
      (Scheme.Modules.pullback q.left).mapIso σ := by
  have hc : GlobalPullbackFrame.comparison g L q (q ≫ g) rfl = (Scheme.Modules.pullbackComp q.left g.left).app L.sheaf := by
    rw [GlobalPullbackFrame.comparison_eq]
    apply Iso.ext
    exact Category.comp_id _
  exact congrArg (fun e : (Scheme.Modules.pullback q.left).obj ((Scheme.Modules.pullback g.left).obj L.sheaf) ≅
      Fibers.fiber L (q ≫ g) => e.symm ≪≫ (Scheme.Modules.pullback q.left).mapIso σ) hc

/-- Evaluation of the actual symmetry commutes with every change of test scheme. -/
theorem natural {T U : Over S} (a : U ⟶ T) (q : T ⟶ E) (q' : U ⟶ E) (hq : a ≫ q = q')
    (hqg : a ≫ (q ≫ g) = q' ≫ g) :
    (Scheme.Modules.pullback a.left).mapIso (atPoint L g σ q) ≪≫ Fibers.fiberPullbackIso L a q q' hq =
      Fibers.fiberPullbackIso L a (q ≫ g) (q' ≫ g) hqg ≪≫ atPoint L g σ q' := by
  let c := GlobalPullbackFrame.comparison g L q (q ≫ g) rfl
  let c' := GlobalPullbackFrame.comparison g L q' (q' ≫ g) rfl
  let F := Scheme.Modules.pullback a.left
  let u := Fibers.fiberPullbackIso (L.pullback g.left) a q q' hq
  let v := Fibers.fiberPullbackIso L a (q ≫ g) (q' ≫ g) hqg
  have hc : F.mapIso c ≪≫ v = u ≪≫ c' := GlobalFrameNaturality.comparison_pullback g L a q (q ≫ g) rfl q' (q' ≫ g) rfl hq hqg
  have hs := FiberIsomorphisms.fiberIso_pullback (S := S) (E := E) (L.pullback g.left) L σ a q q' hq
  have hs' : F.mapIso ((Scheme.Modules.pullback q.left).mapIso σ) ≪≫ Fibers.fiberPullbackIso L a q q' hq =
      u ≪≫ (Scheme.Modules.pullback q'.left).mapIso σ := hs
  exact inverse_functor_square F c ((Scheme.Modules.pullback q.left).mapIso σ)
    c' ((Scheme.Modules.pullback q'.left).mapIso σ) u v (Fibers.fiberPullbackIso L a q q' hq) hc hs'

end

end OAI.AlgebraicGeometry.Picard.PoincareBundle.Line.SymmetryFibers

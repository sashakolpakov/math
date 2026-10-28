import OAI.AlgebraicGeometry.Picard.PoincareBundle.NormalizedKernelTranslation

/-! # Translation Fibers -/

namespace OAI.AlgebraicGeometry.Picard.PoincareBundle.Subgroup.TranslationFibers

noncomputable section

/-! Restrict global subgroup translation to every test scheme, with native pullback compatibility. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj

universe u

open OAI.AlgebraicGeometry.Picard.PoincareBundle.Line.Fibers OAI.AlgebraicGeometry.Picard.PoincareBundle.NormalizedKernelTranslation
open OAI.AlgebraicGeometry.Picard.PoincareBundle.Geometric.KernelLinearization OAI.AlgebraicGeometry.Picard.PoincareBundle.PullHom
open Pseudofunctor.LocallyDiscreteOpToCat

variable {S : Scheme.{u}} {H A : Over S} [GrpObj A]
  (i : H ⟶ A) (L : Line.Bundles.LineBundle A.left)
  (t : Line.Fibers.fiber L (snd H A) ≅ Line.Fibers.fiber L (NormalizedKernelTranslation.action i))

theorem action_pair {T : Over S} (a : T ⟶ H) (x : T ⟶ A) :
    lift a x ≫ NormalizedKernelTranslation.action i = (a ≫ i) * x := by
  rw [NormalizedKernelTranslation.action, ← Category.assoc, lift_map, Category.comp_id]
  rfl

/-- The global isomorphism produces actual isomorphisms of line fibers at all test points. -/
def transportIso {T : Over S} (x y : T ⟶ A) (a : T ⟶ H) (h : (a ≫ i) * x = y) :
    Line.Fibers.fiber L x ≅ Line.Fibers.fiber L y :=
  (Line.Fibers.fiberPullbackIso L (lift a x) (snd H A) x (lift_snd a x)).symm ≪≫
    (Scheme.Modules.pullback (lift a x).left).mapIso t ≪≫
      Line.Fibers.fiberPullbackIso L (lift a x) (NormalizedKernelTranslation.action i) y ((action_pair i a x).trans h)

theorem transportIso_hom {T : Over S} (x y : T ⟶ A) (a : T ⟶ H) (h : (a ≫ i) * x = y) :
    (transportIso i L t x y a h).hom =
      pullHom (F := Geometric.KernelLinearization.overModulePullbacks S) (M₁ := L.sheaf) (M₂ := L.sheaf)
        (f₁ := snd H A) (f₂ := NormalizedKernelTranslation.action i) t.hom (lift a x) x y
        (lift_snd a x) ((action_pair i a x).trans h) :=
  (Line.Fibers.pullHom_eq L (x := snd H A) (y := NormalizedKernelTranslation.action i) t.hom (lift a x) x y
    (lift_snd a x) ((action_pair i a x).trans h)).symm

/-- The induced fiber transport is natural on all test schemes, with no action cocycle assumed. -/
theorem transport_natural {T U : Over S} (g : U ⟶ T)
    (x y : T ⟶ A) (a : T ⟶ H) (h : (a ≫ i) * x = y)
    (x' y' : U ⟶ A) (a' : U ⟶ H) (h' : (a' ≫ i) * x' = y')
    (hx : g ≫ x = x') (hy : g ≫ y = y') (ha : g ≫ a = a') :
    pullHom (F := Geometric.KernelLinearization.overModulePullbacks S) (M₁ := L.sheaf) (M₂ := L.sheaf)
      (f₁ := x) (f₂ := y) (transportIso i L t x y a h).hom g x' y' hx hy =
      (transportIso i L t x' y' a' h').hom := by
  rw [transportIso_hom, transportIso_hom]
  have hp : g ≫ lift a x = lift a' x' := by rw [comp_lift, ha, hx]
  have hn := pullHom_pullHom (F := Geometric.KernelLinearization.overModulePullbacks S) (M₁ := L.sheaf) (M₂ := L.sheaf)
    (f₁ := snd H A) (f₂ := NormalizedKernelTranslation.action i) t.hom (lift a x) x y g x' y'
      (lift_snd a x) ((action_pair i a x).trans h) hx hy
  exact hn.trans (PullHom.pullHom_congr (F := Geometric.KernelLinearization.overModulePullbacks S) (L := L.sheaf) (M := L.sheaf)
    (x := snd H A) (y := NormalizedKernelTranslation.action i) t.hom (g ≫ lift a x) (lift a' x') hp x' y'
    (by rw [Category.assoc, lift_snd, hx])
    (by rw [Category.assoc, action_pair, h, hy])
    (lift_snd a' x') ((action_pair i a' x').trans h'))

end

end OAI.AlgebraicGeometry.Picard.PoincareBundle.Subgroup.TranslationFibers

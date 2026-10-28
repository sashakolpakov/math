import OAI.AlgebraicGeometry.Picard.PoincareBundle.ScaledLineIsomorphisms
import OAI.AlgebraicGeometry.Picard.PoincareBundle.FiberIsomorphismRatios

/-! # Scaled Fiber Isomorphisms -/

namespace OAI.AlgebraicGeometry.Picard.PoincareBundle.ScaledFiberIsomorphisms

noncomputable section

/-! Regular scalar correction preserves the native pullback law of actual fiber isomorphisms. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

open OAI.AlgebraicGeometry.Picard.PoincareBundle.Line.Fibers OAI.AlgebraicGeometry.Picard.PoincareBundle.FiberIsomorphismRatios OAI.AlgebraicGeometry.Picard.PoincareBundle.ScaledLineIsomorphisms OAI.AlgebraicGeometry.Picard.PoincareBundle.Geometric.KernelLinearization
open Pseudofunctor.LocallyDiscreteOpToCat

variable {S : Scheme.{u}} {A : Over S} (L : Line.Bundles.LineBundle A.left)

theorem pullIso_rescale {T U : Over S} {x y : T ⟶ A} (e : Line.Fibers.fiber L x ≅ Line.Fibers.fiber L y)
    (g : U ⟶ T) (x' y' : U ⟶ A) (hx : g ≫ x = x') (hy : g ≫ y = y') (r : Γ(T.left, ⊤)ˣ) :
    FiberIsomorphismRatios.pullIso L (ScaledLineIsomorphisms.rescale e r) g x' y' hx hy =
      ScaledLineIsomorphisms.rescale (FiberIsomorphismRatios.pullIso L e g x' y' hx hy) (Units.map g.left.appTop.hom r) := by
  let p := (Line.Fibers.fiberPullbackIso L g x x' hx).symm
  let q := Line.Fibers.fiberPullbackIso L g y y' hy
  let e' := (Scheme.Modules.pullback g.left).mapIso e
  let r' := Units.map g.left.appTop.hom.toMonoidHom r
  change p ≪≫ (Scheme.Modules.pullback g.left).mapIso (ScaledLineIsomorphisms.rescale e r) ≪≫ q =
    ScaledLineIsomorphisms.rescale (p ≪≫ e' ≪≫ q) r'
  rw [ScaledLineIsomorphisms.rescale_pullback]
  exact (congrArg (fun d => p ≪≫ d) (ScaledLineIsomorphisms.rescale_postcomp e' q r').symm).trans
    (ScaledLineIsomorphisms.rescale_precomp p (e' ≪≫ q) r').symm

theorem rescale_natural {T U : Over S} {x y : T ⟶ A} (e : Line.Fibers.fiber L x ≅ Line.Fibers.fiber L y)
    (g : U ⟶ T) (x' y' : U ⟶ A) (hx : g ≫ x = x') (hy : g ≫ y = y')
    (e' : Line.Fibers.fiber L x' ≅ Line.Fibers.fiber L y') (r : Γ(T.left, ⊤)ˣ) (r' : Γ(U.left, ⊤)ˣ)
    (he : pullHom (F := Geometric.KernelLinearization.overModulePullbacks S) (M₁ := L.sheaf) (M₂ := L.sheaf)
      (f₁ := x) (f₂ := y) e.hom g x' y' hx hy = e'.hom)
    (hr : Units.map g.left.appTop.hom r = r') :
    pullHom (F := Geometric.KernelLinearization.overModulePullbacks S) (M₁ := L.sheaf) (M₂ := L.sheaf)
      (f₁ := x) (f₂ := y) (ScaledLineIsomorphisms.rescale e r).hom g x' y' hx hy = (ScaledLineIsomorphisms.rescale e' r').hom := by
  have he' : FiberIsomorphismRatios.pullIso L e g x' y' hx hy = e' := Iso.ext ((FiberIsomorphismRatios.pullIso_hom L e g x' y' hx hy).trans he)
  have h := (pullIso_rescale L e g x' y' hx hy r).trans (congrArg₂ ScaledLineIsomorphisms.rescale he' hr)
  exact (FiberIsomorphismRatios.pullIso_hom L (ScaledLineIsomorphisms.rescale e r) g x' y' hx hy).symm.trans (congrArg Iso.hom h)

end

end OAI.AlgebraicGeometry.Picard.PoincareBundle.ScaledFiberIsomorphisms

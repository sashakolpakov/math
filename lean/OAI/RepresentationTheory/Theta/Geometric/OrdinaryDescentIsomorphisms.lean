import OAI.AlgebraicGeometry.Picard.PoincareBundle.Geometric.DescentEquations

/-! # Ordinary Descent Isomorphisms -/

namespace OAI.RepresentationTheory.Theta.Geometric.OrdinaryDescentIsomorphisms

noncomputable section

/-! Isomorphisms of ordinary scheme descent data from native module
isomorphisms and their all-test compatibility equation. -/

set_option backward.isDefEq.respectTransparency false
open _root_.CategoryTheory _root_.AlgebraicGeometry

open OAI.AlgebraicGeometry.Picard.PoincareBundle.Geometric.KernelLinearization
universe u

def nativeDescentIsoMk {X Y : Scheme.{u}} (f : X ⟶ Y)
    (D E : AlgebraicGeometry.Picard.PoincareBundle.Geometric.KernelLinearization.modulePullbacks.DescentData (fun (_ : PUnit.{1}) => f))
    (b : D.obj PUnit.unit ≅ E.obj PUnit.unit)
    (hb : ∀ {T : Scheme.{u}} (q : T ⟶ Y) (x y : T ⟶ X)
      (hx : x ≫ f = q) (hy : y ≫ f = q),
      (Scheme.Modules.pullback x).map b.hom ≫ E.hom q x y hx hy =
        D.hom q x y hx hy ≫ (Scheme.Modules.pullback y).map b.hom) : D ≅ E := by
  refine Pseudofunctor.DescentData.isoMk (fun _ => b) ?_
  intro T q a c x y hx hy
  cases a
  cases c
  exact hb q x y hx hy

def nativeDescentObjIso {X Y : Scheme.{u}} (f : X ⟶ Y)
    {D E : AlgebraicGeometry.Picard.PoincareBundle.Geometric.KernelLinearization.modulePullbacks.DescentData (fun (_ : PUnit.{1}) => f)} (e : D ≅ E) :
    D.obj PUnit.unit ≅ E.obj PUnit.unit where
  hom := e.hom.hom PUnit.unit
  inv := e.inv.hom PUnit.unit
  hom_inv_id := congrArg (fun a => a.hom PUnit.unit) e.hom_inv_id
  inv_hom_id := congrArg (fun a => a.hom PUnit.unit) e.inv_hom_id

theorem nativeDescentObjIso_compatible {X Y : Scheme.{u}} (f : X ⟶ Y)
    {D E : AlgebraicGeometry.Picard.PoincareBundle.Geometric.KernelLinearization.modulePullbacks.DescentData (fun (_ : PUnit.{1}) => f)} (e : D ≅ E)
    {T : Scheme.{u}} (q : T ⟶ Y) (x y : T ⟶ X) (hx : x ≫ f = q) (hy : y ≫ f = q) :
    (Scheme.Modules.pullback x).map (nativeDescentObjIso f e).hom ≫ E.hom q x y hx hy =
      D.hom q x y hx hy ≫ (Scheme.Modules.pullback y).map (nativeDescentObjIso f e).hom :=
  e.hom.comm q (i₁ := PUnit.unit) (i₂ := PUnit.unit) x y hx hy

end

end OAI.RepresentationTheory.Theta.Geometric.OrdinaryDescentIsomorphisms

import OAI.AlgebraicGeometry.Divisors.LineBundles.Integral.FiberGenericPoint
import Mathlib.AlgebraicGeometry.Morphisms.UniversallyOpen

/-! # Fiber Composition -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.Integral.FiberComposition.BundleCycles

noncomputable section

/-! # LineBundleCycles: fiber generic points under flat factorizations and actual scheme isomorphisms -/

open _root_.AlgebraicGeometry _root_.CategoryTheory _root_.TopologicalSpace

theorem integralFiberGenericPoint_iso {X Y S : Scheme.{0}}
    (e : X ≅ Y) (p : X ⟶ S) (q : Y ⟶ S)
    [GeometricallyIntegral p] [GeometricallyIntegral q]
    (h : e.hom ≫ q = p) (s : S) :
    e.hom (FiberGenericPoint.BundleCycles.integralFiberGenericPoint p s) = FiberGenericPoint.BundleCycles.integralFiberGenericPoint q s := by
  apply FiberGenericPoint.BundleCycles.integralFiberGenericPoint_unique
  · exact (congrArg (fun k : X ⟶ S => k (FiberGenericPoint.BundleCycles.integralFiberGenericPoint p s)) h).trans
      (FiberGenericPoint.BundleCycles.integralFiberGenericPoint_projection p s)
  · intro y hy
    have hi : e.inv ≫ p = q := by rw [← h, ← Category.assoc, e.inv_hom_id, Category.id_comp]
    have hiy : p (e.inv y) = s := (congrArg (fun k : Y ⟶ S => k y) hi).trans hy
    have hs := (FiberGenericPoint.BundleCycles.integralFiberGenericPoint_specializes p s (e.inv y) hiy).map e.hom.continuous
    simpa using hs

theorem integralFiberGenericPoint_factorization {X W Y S : Scheme.{0}}
    (e : X ≅ W) (p : X ⟶ S) (f : W ⟶ Y) (g : Y ⟶ S)
    [GeometricallyIntegral p] [GeometricallyIntegral f] [GeometricallyIntegral g] [Flat f]
    (h : e.hom ≫ f ≫ g = p) (s : S) :
    e.hom (FiberGenericPoint.BundleCycles.integralFiberGenericPoint p s) =
      FiberGenericPoint.BundleCycles.integralFiberGenericPoint f (FiberGenericPoint.BundleCycles.integralFiberGenericPoint g s) := by
  have hi : e.inv ≫ p = f ≫ g := by
    rw [← h, ← Category.assoc, e.inv_hom_id, Category.id_comp]
  let u := FiberGenericPoint.BundleCycles.integralFiberGenericPoint f (FiberGenericPoint.BundleCycles.integralFiberGenericPoint g s)
  have hu : e.inv u = FiberGenericPoint.BundleCycles.integralFiberGenericPoint p s := by
    apply FiberGenericPoint.BundleCycles.integralFiberGenericPoint_unique
    · change (e.inv ≫ p) u = s
      rw [hi]
      change g (f u) = s
      rw [FiberGenericPoint.BundleCycles.integralFiberGenericPoint_projection, FiberGenericPoint.BundleCycles.integralFiberGenericPoint_projection]
    · intro x hx
      have hbase : g (f (e.hom x)) = s := (congrArg (fun k : X ⟶ S => k x) h).trans hx
      obtain ⟨v, hv, hfv⟩ := Flat.generalizingMap f
        (FiberGenericPoint.BundleCycles.integralFiberGenericPoint_specializes g s (f (e.hom x)) hbase)
      have huv : u ⤳ v := FiberGenericPoint.BundleCycles.integralFiberGenericPoint_specializes f _ v hfv
      have hs := (huv.trans hv).map e.inv.continuous
      simpa using hs
  have he := congrArg e.hom hu
  simpa [u] using he.symm

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.Integral.FiberComposition.BundleCycles

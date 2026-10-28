import OAI.AlgebraicGeometry.Divisors.LineBundles.Integral.FiberGenericPoint
import Mathlib.AlgebraicGeometry.PullbackCarrier

/-! # Fiber Open -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.Integral.FiberOpen.BundleCycles

noncomputable section

section

/-! # LineBundleCycles: actual fiber generic points commute with every scheme pullback square -/

open _root_.AlgebraicGeometry _root_.CategoryTheory _root_.TopologicalSpace

theorem integralFiberGenericPoint_naturality {X Y X' Y' : Scheme.{0}}
    (f : X ⟶ Y) (f' : X' ⟶ Y') (i : Y' ⟶ Y) (j : X' ⟶ X)
    [GeometricallyIntegral f] [GeometricallyIntegral f'] (h : IsPullback f' j i f) (y : Y') :
    j (FiberGenericPoint.BundleCycles.integralFiberGenericPoint f' y) = FiberGenericPoint.BundleCycles.integralFiberGenericPoint f (i y) := by
  apply FiberGenericPoint.BundleCycles.integralFiberGenericPoint_unique
  · exact (congrArg (fun k => k (FiberGenericPoint.BundleCycles.integralFiberGenericPoint f' y)) h.w).symm.trans
      (congrArg i (FiberGenericPoint.BundleCycles.integralFiberGenericPoint_projection f' y))
  · intro z hz
    obtain ⟨w, hw₁, hw₂⟩ := Scheme.exists_preimage_of_isPullback h y z hz.symm
    exact hw₂ ▸ (FiberGenericPoint.BundleCycles.integralFiberGenericPoint_specializes f' y w hw₁).map j.continuous

theorem integralFiberCycleExtension_naturality {X Y X' Y' : Scheme.{0}}
    (f : X ⟶ Y) (f' : X' ⟶ Y') (i : Y' ⟶ Y) (j : X' ⟶ X)
    [GeometricallyIntegral f] [GeometricallyIntegral f'] (h : IsPullback f' j i f) (z : Y' →₀ ℚ) :
    Finsupp.mapDomain j (FiberGenericPoint.BundleCycles.integralFiberCycleExtension f' z) =
      FiberGenericPoint.BundleCycles.integralFiberCycleExtension f (Finsupp.mapDomain i z) := by
  change Finsupp.mapDomain j (Finsupp.mapDomain (FiberGenericPoint.BundleCycles.integralFiberGenericPoint f') z) =
    Finsupp.mapDomain (FiberGenericPoint.BundleCycles.integralFiberGenericPoint f) (Finsupp.mapDomain i z)
  rw [← Finsupp.mapDomain_comp, ← Finsupp.mapDomain_comp]
  exact congrArg (fun k => Finsupp.mapDomain k z)
    (funext (integralFiberGenericPoint_naturality f f' i j h))

end

section

/-! # LineBundleCycles: actual fiber-generic cycle extension commutes with open restriction -/

open _root_.AlgebraicGeometry _root_.CategoryTheory

theorem integralFiberCycleExtension_openRestriction {E X E' U : Scheme.{0}}
    (p : E ⟶ X) (q : E' ⟶ U) [GeometricallyIntegral p] [GeometricallyIntegral q]
    (i : U ⟶ X) (j : E' ⟶ E) [IsOpenImmersion i] [IsOpenImmersion j]
    (h : IsPullback q j i p) (z : X →₀ ℚ) :
    Finsupp.comapDomain j (FiberGenericPoint.BundleCycles.integralFiberCycleExtension p z) j.isOpenEmbedding.injective.injOn =
      FiberGenericPoint.BundleCycles.integralFiberCycleExtension q (Finsupp.comapDomain i z i.isOpenEmbedding.injective.injOn) := by
  ext a
  change Finsupp.mapDomain (FiberGenericPoint.BundleCycles.integralFiberGenericPoint p) z (j a) =
    Finsupp.mapDomain (FiberGenericPoint.BundleCycles.integralFiberGenericPoint q)
      (Finsupp.comapDomain i z i.isOpenEmbedding.injective.injOn) a
  by_cases ha : a ∈ Set.range (FiberGenericPoint.BundleCycles.integralFiberGenericPoint q)
  · obtain ⟨u, rfl⟩ := ha
    rw [integralFiberGenericPoint_naturality p q i j h,
      Finsupp.mapDomain_apply_of_injective (FiberGenericPoint.BundleCycles.integralFiberGenericPoint_injective p),
      Finsupp.mapDomain_apply_of_injective (FiberGenericPoint.BundleCycles.integralFiberGenericPoint_injective q)]
    rfl
  · have hj : j a ∉ Set.range (FiberGenericPoint.BundleCycles.integralFiberGenericPoint p) := by
      rintro ⟨x, hx⟩
      have hb : i (q a) = x :=
        (congrArg (fun k : E' ⟶ X => k a) h.w).trans
          ((congrArg p hx.symm).trans (FiberGenericPoint.BundleCycles.integralFiberGenericPoint_projection p x))
      have he := integralFiberGenericPoint_naturality p q i j h (q a)
      rw [hb] at he
      exact ha ⟨q a, j.isOpenEmbedding.injective (he.trans hx)⟩
    rw [Finsupp.mapDomain_of_notMem_range _ _ hj, Finsupp.mapDomain_of_notMem_range _ _ ha]

end

/-! Fiber generic points and cycle extension commute with a square
of open immersions, even when the source open is only part of the inverse image. -/

open _root_.AlgebraicGeometry _root_.CategoryTheory

variable {E X E' U : Scheme.{0}}
    (p : E ⟶ X) (q : E' ⟶ U) [GeometricallyIntegral p] [GeometricallyIntegral q]
    (i : U ⟶ X) (j : E' ⟶ E) [IsOpenImmersion i] [IsOpenImmersion j]
    (h : q ≫ i = j ≫ p)

include h in
theorem integralFiberGenericPoint_openSquare (u : U) :
    j (FiberGenericPoint.BundleCycles.integralFiberGenericPoint q u) = FiberGenericPoint.BundleCycles.integralFiberGenericPoint p (i u) := by
  have hp : p (j (FiberGenericPoint.BundleCycles.integralFiberGenericPoint q u)) = i u :=
    (congrArg (fun f : E' ⟶ X => f (FiberGenericPoint.BundleCycles.integralFiberGenericPoint q u)) h).symm.trans
      (congrArg i (FiberGenericPoint.BundleCycles.integralFiberGenericPoint_projection q u))
  have hs := FiberGenericPoint.BundleCycles.integralFiberGenericPoint_specializes p (i u) (j (FiberGenericPoint.BundleCycles.integralFiberGenericPoint q u)) hp
  have hm : FiberGenericPoint.BundleCycles.integralFiberGenericPoint p (i u) ∈ j.opensRange :=
    hs.mem_open j.opensRange.isOpen ⟨FiberGenericPoint.BundleCycles.integralFiberGenericPoint q u, rfl⟩
  obtain ⟨a, ha⟩ := hm
  have hqa : q a = u := by
    apply i.isOpenEmbedding.injective
    exact (congrArg (fun f : E' ⟶ X => f a) h).trans
      ((congrArg p ha).trans (FiberGenericPoint.BundleCycles.integralFiberGenericPoint_projection p (i u)))
  have ht : j (FiberGenericPoint.BundleCycles.integralFiberGenericPoint q u) ⤳ FiberGenericPoint.BundleCycles.integralFiberGenericPoint p (i u) :=
    ha ▸ (FiberGenericPoint.BundleCycles.integralFiberGenericPoint_specializes q u a hqa).map j.continuous
  exact (ht.antisymm hs).eq

include h in
theorem integralFiberCycleExtension_openSquare (z : X →₀ ℚ) :
    Finsupp.comapDomain j (FiberGenericPoint.BundleCycles.integralFiberCycleExtension p z) j.isOpenEmbedding.injective.injOn =
      FiberGenericPoint.BundleCycles.integralFiberCycleExtension q (Finsupp.comapDomain i z i.isOpenEmbedding.injective.injOn) := by
  ext a
  change Finsupp.mapDomain (FiberGenericPoint.BundleCycles.integralFiberGenericPoint p) z (j a) =
    Finsupp.mapDomain (FiberGenericPoint.BundleCycles.integralFiberGenericPoint q)
      (Finsupp.comapDomain i z i.isOpenEmbedding.injective.injOn) a
  by_cases ha : a ∈ Set.range (FiberGenericPoint.BundleCycles.integralFiberGenericPoint q)
  · obtain ⟨u, rfl⟩ := ha
    rw [integralFiberGenericPoint_openSquare p q i j h,
      Finsupp.mapDomain_apply_of_injective (FiberGenericPoint.BundleCycles.integralFiberGenericPoint_injective p),
      Finsupp.mapDomain_apply_of_injective (FiberGenericPoint.BundleCycles.integralFiberGenericPoint_injective q)]
    rfl
  · have hj : j a ∉ Set.range (FiberGenericPoint.BundleCycles.integralFiberGenericPoint p) := by
      rintro ⟨x, hx⟩
      have hb : i (q a) = x :=
        (congrArg (fun k : E' ⟶ X => k a) h).trans
          ((congrArg p hx.symm).trans (FiberGenericPoint.BundleCycles.integralFiberGenericPoint_projection p x))
      have he := integralFiberGenericPoint_openSquare p q i j h (q a)
      rw [hb] at he
      exact ha ⟨q a, j.isOpenEmbedding.injective (he.trans hx)⟩
    rw [Finsupp.mapDomain_of_notMem_range _ _ hj, Finsupp.mapDomain_of_notMem_range _ _ ha]

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.Integral.FiberOpen.BundleCycles

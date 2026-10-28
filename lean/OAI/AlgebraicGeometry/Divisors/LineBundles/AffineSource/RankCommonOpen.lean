import OAI.AlgebraicGeometry.Divisors.LineBundles.AffineSpace.SourceRank

/-! # Rank Common Open -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.AffineSource.RankCommonOpen.BundleCycles

noncomputable section

section

/-! Relative ranks agree on a nonempty common open chart, as follows
from the actual dimensions of its integral fiber supports. -/

open _root_.AlgebraicGeometry _root_.CategoryTheory

variable {E X E' U : Scheme.{0}} [AlgebraicGeometry.IsNoetherian X]
    [AlgebraicGeometry.IsNoetherian E']
    [AlgebraicGeometry.IsNoetherian U]
    (p : E ⟶ X) (q : E' ⟶ U) [GeometricallyIntegral p] [GeometricallyIntegral q]
    (i : U ⟶ X) (j : E' ⟶ E) [IsOpenImmersion i] [IsOpenImmersion j]
    (hs : q ≫ i = j ≫ p) (f : X ⟶ Foundations.Scheme.ProjectiveSpace.complexBase) [LocallyOfFiniteType f]
    (r s : ℕ) (hp : AffineSpace.SourceRank.BundleCycles.HasAffineSpaceSourceChartsOfRank p r) (hq : AffineSpace.SourceRank.BundleCycles.HasAffineSpaceSourceChartsOfRank q s)

include hp hq hs f in
theorem affineSpaceSourceRank_openSquare (u : U) : r = s := by
  have H := AffineSpace.SourceRank.BundleCycles.affineSpaceSourceFiberGenericPoint_dimension p f r hp (i u)
  rw [← Integral.FiberOpen.BundleCycles.integralFiberGenericPoint_openSquare p q i j hs u, ImmersionDimension.BundleCycles.pointClosure_dimension_immersion j] at H
  have he : j ≫ (p ≫ f) = q ≫ (i ≫ f) := by rw [← Category.assoc, ← hs, Category.assoc]
  rw [he, AffineSpace.SourceRank.BundleCycles.affineSpaceSourceFiberGenericPoint_dimension q (i ≫ f) s hq,
    ImmersionDimension.BundleCycles.pointClosure_dimension_immersion i] at H
  omega

end

/-! Two open presentations of the same integral ambient fibers
have the same relative dimension, by comparing their generic points. -/

open _root_.AlgebraicGeometry _root_.CategoryTheory

variable {E A B X U : Scheme.{0}} [AlgebraicGeometry.IsNoetherian X]
    [AlgebraicGeometry.IsNoetherian U] [AlgebraicGeometry.IsNoetherian A]
    [AlgebraicGeometry.IsNoetherian B]
    (p : E ⟶ X) (q : A ⟶ X) (t : B ⟶ U)
    [GeometricallyIntegral p] [GeometricallyIntegral q] [GeometricallyIntegral t]
    (j : A ⟶ E) (k : B ⟶ E) (i : U ⟶ X)
    [IsOpenImmersion j] [IsOpenImmersion k] [IsOpenImmersion i]
    (hj : j ≫ p = q) (hk : t ≫ i = k ≫ p)
    (f : X ⟶ Foundations.Scheme.ProjectiveSpace.complexBase) [LocallyOfFiniteType f]
    (r s : ℕ) (hq : AffineSpace.SourceRank.BundleCycles.HasAffineSpaceSourceChartsOfRank q r)
    (ht : AffineSpace.SourceRank.BundleCycles.HasAffineSpaceSourceChartsOfRank t s)

include hj hk f hq ht in
theorem affineSpaceSourceRank_commonOpen (u : U) : r = s := by
  have ha : j (Integral.FiberGenericPoint.BundleCycles.integralFiberGenericPoint q (i u)) = Integral.FiberGenericPoint.BundleCycles.integralFiberGenericPoint p (i u) :=
    Integral.FiberOpen.BundleCycles.integralFiberGenericPoint_openSquare p q (𝟙 X) j (by rw [Category.comp_id, hj]) (i u)
  have hb := Integral.FiberOpen.BundleCycles.integralFiberGenericPoint_openSquare p t i k hk u
  have H := congrArg (fun z : E =>
    Foundations.Scheme.SupportDimension.supportTranscendenceDimension (irreducibleSetEquivPoints.symm z) (p ≫ f)) (ha.trans hb.symm)
  rw [ImmersionDimension.BundleCycles.pointClosure_dimension_immersion j, ImmersionDimension.BundleCycles.pointClosure_dimension_immersion k] at H
  have hjf : j ≫ (p ≫ f) = q ≫ f := by rw [← Category.assoc, hj]
  have hkf : k ≫ (p ≫ f) = t ≫ (i ≫ f) := by rw [← Category.assoc, ← hk, Category.assoc]
  rw [hjf, hkf, AffineSpace.SourceRank.BundleCycles.affineSpaceSourceFiberGenericPoint_dimension q f r hq,
    AffineSpace.SourceRank.BundleCycles.affineSpaceSourceFiberGenericPoint_dimension t (i ≫ f) s ht,
    ImmersionDimension.BundleCycles.pointClosure_dimension_immersion i] at H
  omega

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.AffineSource.RankCommonOpen.BundleCycles

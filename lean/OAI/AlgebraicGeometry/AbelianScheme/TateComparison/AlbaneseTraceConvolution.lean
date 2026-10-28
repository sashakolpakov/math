import OAI.AlgebraicGeometry.AbelianScheme.TateComparison.GeometricConvolution
import OAI.AlgebraicGeometry.AbelianScheme.TateComparison.AlbaneseTrace
import OAI.AlgebraicGeometry.AbelianScheme.TateComparison.TraceLaws
import OAI.AlgebraicGeometry.AbelianScheme.TateComparison.Interface

/-! # Albanese Trace Convolution -/

namespace OAI.AlgebraicGeometry.AbelianScheme.TateComparison

noncomputable section

/-! Geometric convolution gives an equality of the actual global
algebraic trace maps into the Albanese. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj Classical

def AlbaneseTraceConvolution.multisetPointSumHom {X A : Type*} [AddCommMonoid A] (f : X → A) : Multiset X →+ A where
  toFun m := (m.map f).sum
  map_zero' := rfl
  map_add' a b := by rw [Multiset.map_add, Multiset.sum_add]

variable {E K : Type} [Field E] [NumberField E] [NumberField.IsCMField E]
  [Field K] [NumberField K] {s q : ℕ} [Fact q.Prime]
  (D : Data.SphericalPELAlbaneseData E K s q) (hg : D.IsGoodCompletelySplitPrime)
  (hdegree : Module.finrank ℚ E = 2 * s) (hs : 0 < s)
  (hgeometry : D.HasIntegralModelGeometry) (hIsogenyQuotient : D.RealizesIsogenyQuotient) (hElementaryDivisors : Duality.ElementaryDivisorsInput ℤ_[q] ℚ_[q])

include hg hdegree hs hgeometry hIsogenyQuotient hElementaryDivisors in
theorem Data.SphericalPELAlbaneseData.neighbor_albanese_sum_convolution (u v : Local.IntegralType s)
    {k : Type} [Field k] [IsAlgClosed k]
    (b : Spec (.of k) ⟶ Spec (.of K)) (x : D.GeometricPoint b) :
    ((D.neighbors u b x).map (fun y => ((D.neighbors v b y).map (D.aTotalPoint hgeometry)).sum)).sum =
      (ConvolutionCoefficients.convolutionCoefficients s q hElementaryDivisors u v).sum (fun w n =>
        n • ((D.neighbors w b x).map (D.aTotalPoint hgeometry)).sum) := by
  have h := congrArg (AlbaneseTraceConvolution.multisetPointSumHom (D.aTotalPoint hgeometry))
    (D.neighbors_convolution hg hdegree hs hgeometry hIsogenyQuotient hElementaryDivisors u v b x)
  simp only [map_finsuppSum, map_nsmul] at h
  change (((D.neighbors u b x).bind (D.neighbors v b)).map (D.aTotalPoint hgeometry)).sum = _ at h
  rw [Multiset.map_bind, Multiset.sum_bind] at h
  exact h

theorem Data.SphericalPELAlbaneseData.albaneseTrace_point_sum (t : Local.IntegralType s)
    {k : Type} [Field k] [IsAlgClosed k]
    (b : Spec (.of k) ⟶ Spec (.of K)) (x : D.GeometricPoint b) :
    Additive.ofMul (x ≫ D.albaneseTrace hgeometry t) =
      ((D.neighbors t b x).map (D.aTotalPoint hgeometry)).sum := by
  rw [D.albaneseTrace_geometric hgeometry t b x]
  rfl

include hg hdegree hs hIsogenyQuotient hElementaryDivisors in
theorem Data.SphericalPELAlbaneseData.albaneseTrace_convolution (u v : Local.IntegralType s) :
    let : IsReduced D.space.left := D.genericSpace_reduced hgeometry
    let : IsLocallyNoetherian D.space.left := D.genericSpace_locallyNoetherian hgeometry
    let : IsSeparated D.albaneseGroup.X.hom := D.albaneseGroup_separated hgeometry
    Additive.ofMul ((D.correspondence u).algebraicTrace (D.albaneseTrace hgeometry v)) =
      (ConvolutionCoefficients.convolutionCoefficients s q hElementaryDivisors u v).sum
        (fun w n => n • Additive.ofMul (D.albaneseTrace hgeometry w)) := by
  have : IsReduced D.space.left := D.genericSpace_reduced hgeometry
  have : IsLocallyNoetherian D.space.left := D.genericSpace_locallyNoetherian hgeometry
  have : IsSeparated D.albaneseGroup.X.hom := D.albaneseGroup_separated hgeometry
  apply Additive.toMul.injective
  apply GeometricExt.over_hom_ext_geometric
  intro k _ _ b x
  apply Additive.ofMul.injective
  let e : Additive (D.space ⟶ D.albaneseGroup.X) →+
      Additive (Over.mk b ⟶ D.albaneseGroup.X) :=
    ((yonedaGrpObj D.albaneseGroup.X).map x.op).hom.toAdditive
  have h := D.neighbor_albanese_sum_convolution hg hdegree hs hgeometry hIsogenyQuotient hElementaryDivisors u v b x
  change Additive.ofMul (x ≫ (D.correspondence u).algebraicTrace (D.albaneseTrace hgeometry v)) =
    e ((ConvolutionCoefficients.convolutionCoefficients s q hElementaryDivisors u v).sum _)
  have hx : Additive.ofMul (x ≫ (D.correspondence u).algebraicTrace (D.albaneseTrace hgeometry v)) =
      ((D.neighbors u b x).map (fun y => Additive.ofMul (y ≫ D.albaneseTrace hgeometry v))).sum :=
    congrArg Additive.ofMul ((D.correspondence u).algebraicTrace_geometric
      (D.albaneseTrace hgeometry v) b x)
  refine hx.trans ?_
  rw [map_finsuppSum]
  simp only [map_nsmul]
  change (((D.neighbors u b x).map (fun y => Additive.ofMul (y ≫ D.albaneseTrace hgeometry v))).sum) =
    (ConvolutionCoefficients.convolutionCoefficients s q hElementaryDivisors u v).sum (fun w n => n • Additive.ofMul (x ≫ D.albaneseTrace hgeometry w))
  have hl := congrArg (fun f : D.GeometricPoint b → Additive (Over.mk b ⟶ D.albaneseGroup.X) =>
    ((D.neighbors u b x).map f).sum) (funext (D.albaneseTrace_point_sum hgeometry v b))
  refine hl.trans (h.trans ?_)
  apply Finsupp.sum_congr
  intro w _
  exact congrArg (fun z => ConvolutionCoefficients.convolutionCoefficients s q hElementaryDivisors u v w • z)
    (D.albaneseTrace_point_sum hgeometry w b x).symm

end

end OAI.AlgebraicGeometry.AbelianScheme.TateComparison

import OAI.AlgebraicGeometry.AbelianScheme.TateComparison.HeckeNormalizationDefect
import OAI.AlgebraicGeometry.AbelianScheme.TateComparison.IntegralEndEvaluation
import OAI.AlgebraicGeometry.AbelianScheme.TateComparison.CoefficientUniqueness

/-! # Integral Hecke Convolution -/

namespace OAI.AlgebraicGeometry.AbelianScheme.TateComparison

noncomputable section

/-! The actual integral Albanese endomorphisms obey the ordinary raw
Hecke convolution law, with its natural multiplicities. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj

variable {E K : Type} [Field E] [NumberField E] [NumberField.IsCMField E]
  [Field K] [NumberField K] {s q : ℕ} [Fact q.Prime]
  (D : Data.SphericalPELAlbaneseData E K s q) (hg : D.IsGoodCompletelySplitPrime)
  (hdegree : Module.finrank ℚ E = 2 * s) (hs : 0 < s)
  (hgeometry : D.HasIntegralModelGeometry) (hIsogenyQuotient : D.RealizesIsogenyQuotient) (hElementaryDivisors : Duality.ElementaryDivisorsInput ℤ_[q] ℚ_[q])

local instance Data.SphericalPELAlbaneseData.IntegralHeckeConvolution_local1 : GrpObj D.albaneseGroup.X := D.albaneseGroup.grp
local instance Data.SphericalPELAlbaneseData.IntegralHeckeConvolution_local2 : IsCommMonObj D.albaneseGroup.X := D.albaneseGroup.comm

include hg hdegree hs hIsogenyQuotient hElementaryDivisors in
theorem Data.SphericalPELAlbaneseData.heckeEnd_convolution_chronological (u v : Local.IntegralType s) :
    D.heckeEnd hgeometry v * D.heckeEnd hgeometry u =
      (ConvolutionCoefficients.convolutionCoefficients s q hElementaryDivisors u v).sum (fun w n => n • D.heckeEnd hgeometry w) := by
  have : IsReduced D.space.left := D.genericSpace_reduced hgeometry
  have : IsLocallyNoetherian D.space.left := D.genericSpace_locallyNoetherian hgeometry
  have : IsSeparated D.albaneseGroup.X.hom := D.albaneseGroup_separated hgeometry
  apply D.end_eq_of_component_differences hgeometry
  intro k _ _ b j x y
  let z := D.aPoint hgeometry j x - D.aPoint hgeometry j y
  let ev := D.endPointEvaluation z
  let dv : Additive (D.space ⟶ D.albaneseGroup.X) →+
      Additive (Over.mk b ⟶ D.albaneseGroup.X) :=
    IntegralEndEvaluation.pointDifferenceEvaluation (x ≫ D.componentInclusion j) (y ≫ D.componentInclusion j)
  have ht (w : Local.IntegralType s) : D.endPoint (D.heckeEnd hgeometry w) z =
      dv (Additive.ofMul (D.albaneseTrace hgeometry w)) := by
    simpa only [z, dv, IntegralEndEvaluation.pointDifferenceEvaluation_apply, Data.SphericalPELAlbaneseData.endPoint, Data.SphericalPELAlbaneseData.aPoint, Data.SphericalPELAlbaneseData.aTotalPoint,
      toMul_sub, toMul_ofMul, Category.assoc] using
      congrArg Additive.ofMul (D.heckeEnd_differences hgeometry w j x y)
  have hc : D.endPoint (D.heckeEnd hgeometry v)
      (dv (Additive.ofMul (D.albaneseTrace hgeometry u))) =
        dv (Additive.ofMul ((D.correspondence u).algebraicTrace (D.albaneseTrace hgeometry v))) := by
    simpa only [dv, IntegralEndEvaluation.pointDifferenceEvaluation_apply, Data.SphericalPELAlbaneseData.endPoint, toMul_ofMul, Category.assoc] using
      congrArg Additive.ofMul (D.heckeEnd_trace_differences hgeometry u v j x y)
  change ev (D.heckeEnd hgeometry v * D.heckeEnd hgeometry u) = ev _
  calc
    _ = D.endPoint (D.heckeEnd hgeometry v) (D.endPoint (D.heckeEnd hgeometry u) z) :=
      D.endPoint_mul _ _ z
    _ = dv (Additive.ofMul ((D.correspondence u).algebraicTrace (D.albaneseTrace hgeometry v))) := by
      rw [ht, hc]
    _ = dv ((ConvolutionCoefficients.convolutionCoefficients s q hElementaryDivisors u v).sum
        (fun w n => n • Additive.ofMul (D.albaneseTrace hgeometry w))) :=
      congrArg dv (D.albaneseTrace_convolution hg hdegree hs hgeometry hIsogenyQuotient hElementaryDivisors u v)
    _ = (ConvolutionCoefficients.convolutionCoefficients s q hElementaryDivisors u v).sum (fun w n => n • ev (D.heckeEnd hgeometry w)) := by
      rw [map_finsuppSum]
      apply Finsupp.sum_congr
      intro w _
      rw [map_nsmul]
      exact congrArg (fun a => ConvolutionCoefficients.convolutionCoefficients s q hElementaryDivisors u v w • a) (ht w).symm
    _ = _ := by rw [map_finsuppSum]; simp only [map_nsmul]

include hg hdegree hs hIsogenyQuotient in
theorem Data.SphericalPELAlbaneseData.heckeEnd_convolution (u v : Local.IntegralType s) :
    D.heckeEnd hgeometry u * D.heckeEnd hgeometry v =
      (ConvolutionCoefficients.convolutionCoefficients s q hElementaryDivisors u v).sum (fun w n => n • D.heckeEnd hgeometry w) := by
  rw [D.heckeEnd_convolution_chronological hg hdegree hs hgeometry hIsogenyQuotient hElementaryDivisors,
    CoefficientUniqueness.convolutionCoefficients_comm s q hElementaryDivisors v u]

end

end OAI.AlgebraicGeometry.AbelianScheme.TateComparison

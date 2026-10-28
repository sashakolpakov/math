import OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicTruncated.TopEdge
import OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.IntrinsicCohomology

/-! # Cohomology -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison

noncomputable section

/-! The actual good-reduction models compute the original bounded
crystalline Ext groups. Their top-form edge is surjective onto those
same groups. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {K : Type} [Field K] [NumberField K]
  {q : ℕ} [Fact q.Prime] {jq : K →+* ℚ_[q]} (A : Geometry.AbelianH1Model K q jq)

abbrev Geometry.AbelianH1Model.NativeBoundedCrystallineCohomology (n i : ℕ) :=
  IntegralComparison.BoundedCrystalline.CrystallineCohomology.Cohomology (p := q)
    (J := Ideal.span {(q : WittVector q (ZMod q))})
    (δ := AlgebraicGeometry.Crystalline.Cohomology.Witt.DividedPowers.WittDividedPowers.wittDividedPowers q (ZMod q))
    (IntegralComparison.Witt.Crystalline.wittStructureMap q (ZMod q) A.specialFiber.scheme) n i

def Geometry.AbelianH1Model.truncatedCrystallineComparison (n i : ℕ) :
    (AlgebraicGeometry.Crystalline.Cohomology.Base.SmallDeRhamCech.BaseSmallDeRhamCech.total (IntrinsicTruncated.TruncatedModel.NativeTruncatedBase.Ring q n)
      (A.truncatedModel n).scheme).homology i ≃+
        A.NativeBoundedCrystallineCohomology n i :=
  IntegralComparison.TruncatedModel.IntrinsicCohomology.Intrinsic.comparisonEquiv q (ZMod q) n
    (A.truncatedModel n).scheme A.specialFiber.scheme (A.truncatedReduction n)
    (A.truncatedReductionSquare n) (injectiveResolution _) i

def Geometry.AbelianH1Model.truncatedCrystallineTopEdge (n : ℕ) : A.TruncatedSmallTopForms n →+
    A.NativeBoundedCrystallineCohomology n (A.dimension + A.dimension) :=
  (A.truncatedCrystallineComparison n (A.dimension + A.dimension)).toAddMonoidHom.comp
    (A.truncatedTopEdge n).toAddMonoidHom

theorem Geometry.AbelianH1Model.truncatedCrystallineTopEdge_surjective (n : ℕ) :
    Function.Surjective (A.truncatedCrystallineTopEdge n) :=
  (A.truncatedCrystallineComparison n (A.dimension + A.dimension)).surjective.comp
    (A.truncatedTopEdge_surjective n)

end

end OAI.NumberTheory.PadicHodge.GeometricComparison

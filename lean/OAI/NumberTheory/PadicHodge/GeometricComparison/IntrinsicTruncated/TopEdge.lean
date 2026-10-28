import OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicTruncated.Projectivity
import OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicTruncated.Bounds
import OAI.NumberTheory.PadicHodge.IntegralComparison.Small.IntrinsicDeRhamTotal
import OAI.NumberTheory.PadicHodge.IntegralComparison.IntrinsicDeRham.TopEdge

/-! # Top Edge -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison

noncomputable section

/-! The actual finite-level model's top-form cohomology surjects onto
its native de Rham Čech cohomology in the top degree. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

variable {K : Type} [Field K] [NumberField K]
  {q : ℕ} [Fact q.Prime] {jq : K →+* ℚ_[q]} (A : Geometry.AbelianH1Model K q jq)

def Geometry.AbelianH1Model.truncatedSmallCover (n : ℕ) :=
  AlgebraicGeometry.Crystalline.Cohomology.Base.SmallDeRhamCech.BaseSmallDeRhamCech.opens (IntrinsicTruncated.TruncatedModel.NativeTruncatedBase.Ring q n) (A.truncatedModel n).scheme

theorem Geometry.AbelianH1Model.truncatedSmallCover_top (n : ℕ) : (⨆ i, A.truncatedSmallCover n i) = ⊤ :=
  AlgebraicGeometry.Crystalline.Cohomology.Base.SmallEtaleCover.BaseSmallEtaleCover.cover (IntrinsicTruncated.TruncatedModel.NativeTruncatedBase.Ring q n) (A.truncatedModel n).scheme

theorem Geometry.AbelianH1Model.truncatedSmallCover_affine (n : ℕ)
    (i : AlgebraicGeometry.Crystalline.Cohomology.Base.SmallEtaleCover.BaseSmallEtaleCover.Index (IntrinsicTruncated.TruncatedModel.NativeTruncatedBase.Ring q n) (A.truncatedModel n).scheme) :
    IsAffineOpen (A.truncatedSmallCover n i) :=
  (AlgebraicGeometry.Crystalline.Cohomology.Base.SmallEtaleCover.BaseSmallEtaleCover.opens (IntrinsicTruncated.TruncatedModel.NativeTruncatedBase.Ring q n) (A.truncatedModel n).scheme i).property

abbrev Geometry.AbelianH1Model.TruncatedSmallTopForms (n : ℕ) :=
  IntegralComparison.IntrinsicDeRham.TopEdge.Intrinsic.source (IntrinsicTruncated.TruncatedModel.NativeTruncatedBase.Ring q n)
    (A.truncatedModel n).scheme (A.truncatedSmallCover n) A.dimension

def Geometry.AbelianH1Model.truncatedTopEdge (n : ℕ) : A.TruncatedSmallTopForms n →ₗ[IntrinsicTruncated.TruncatedModel.NativeTruncatedBase.Ring q n]
    (AlgebraicGeometry.Crystalline.Cohomology.Base.SmallDeRhamCech.BaseSmallDeRhamCech.total (IntrinsicTruncated.TruncatedModel.NativeTruncatedBase.Ring q n)
      (A.truncatedModel n).scheme).homology (A.dimension + A.dimension) :=
  IntegralComparison.IntrinsicDeRham.TopEdge.Intrinsic.map (IntrinsicTruncated.TruncatedModel.NativeTruncatedBase.Ring q n)
    (A.truncatedModel n).scheme (A.truncatedSmallCover n) A.dimension

theorem Geometry.AbelianH1Model.truncatedTopEdge_surjective (n : ℕ) : Function.Surjective (A.truncatedTopEdge n) :=
  IntegralComparison.IntrinsicDeRham.TopEdge.Intrinsic.surjective (IntrinsicTruncated.TruncatedModel.NativeTruncatedBase.Ring q n)
    (A.truncatedModel n).scheme (A.truncatedSmallCover n) A.dimension
    (A.truncatedSmallCover_top n) (A.truncatedSmallCover_affine n)
    (A.truncatedModel_dimension_le n)

end

end OAI.NumberTheory.PadicHodge.GeometricComparison

import OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicTruncated.Cohomology
import OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicTruncated.EtaleGeometry

/-! # Shift Cohomology -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison

noncomputable section

/-! The actual finite-etale source lift computes the same original
bounded crystalline cohomology as the fixed good-reduction model.
Its top-form edge also surjects onto that original group. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry _root_.TopologicalSpace

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {K : Type} [Field K] [NumberField K]
  {q : ℕ} [Fact q.Prime] {jq : K →+* ℚ_[q]} (A : Geometry.AbelianH1Model K q jq)
  (n m : ℕ) (hm : ¬q ∣ m)

instance Geometry.AbelianH1Model.truncatedShiftModel_separated : (A.truncatedShiftModel n m hm).left.IsSeparated := by
  constructor
  rw [← terminal.comp_from (A.truncatedShiftModel n m hm).hom]
  infer_instance

instance Geometry.AbelianH1Model.truncatedShiftModel_noetherianSpace : NoetherianSpace (A.truncatedShiftModel n m hm).left := by
  let : IsLocallyNoetherian (A.truncatedShiftModel n m hm).left :=
    LocallyOfFiniteType.isLocallyNoetherian (A.truncatedShiftModel n m hm).hom
  let : CompactSpace (A.truncatedShiftModel n m hm).left :=
    QuasiCompact.compactSpace_of_compactSpace (A.truncatedShiftModel n m hm).hom
  let : IsNoetherian (A.truncatedShiftModel n m hm).left := {}
  infer_instance

theorem Geometry.AbelianH1Model.truncatedShiftModel_dimension_le :
    topologicalKrullDim (A.truncatedShiftModel n m hm).left ≤ (A.dimension : WithBot ℕ∞) :=
  IntegralComparison.Smooth.ThickeningCohomologyBound.thickening_dimension_le
    A.specialFiber.scheme A.dimension (A.truncatedShiftReduction n m hm)

def Geometry.AbelianH1Model.truncatedShiftOver : A.truncatedShiftModel n m hm ⟶ (A.truncatedModel n).scheme :=
  Over.homMk (A.truncatedShiftMap n m hm) rfl

def Geometry.AbelianH1Model.truncatedShiftSmallCover :=
  AlgebraicGeometry.Crystalline.Cohomology.Base.SmallDeRhamCech.BaseSmallDeRhamCech.opens (IntrinsicTruncated.TruncatedModel.NativeTruncatedBase.Ring q n) (A.truncatedShiftModel n m hm)

theorem Geometry.AbelianH1Model.truncatedShiftSmallCover_top : (⨆ i, A.truncatedShiftSmallCover n m hm i) = ⊤ :=
  AlgebraicGeometry.Crystalline.Cohomology.Base.SmallEtaleCover.BaseSmallEtaleCover.cover (IntrinsicTruncated.TruncatedModel.NativeTruncatedBase.Ring q n) (A.truncatedShiftModel n m hm)

theorem Geometry.AbelianH1Model.truncatedShiftSmallCover_affine
    (i : AlgebraicGeometry.Crystalline.Cohomology.Base.SmallEtaleCover.BaseSmallEtaleCover.Index (IntrinsicTruncated.TruncatedModel.NativeTruncatedBase.Ring q n) (A.truncatedShiftModel n m hm)) :
    IsAffineOpen (A.truncatedShiftSmallCover n m hm i) :=
  (AlgebraicGeometry.Crystalline.Cohomology.Base.SmallEtaleCover.BaseSmallEtaleCover.opens (IntrinsicTruncated.TruncatedModel.NativeTruncatedBase.Ring q n) (A.truncatedShiftModel n m hm) i).property

abbrev Geometry.AbelianH1Model.TruncatedShiftSmallTopForms :=
  IntegralComparison.IntrinsicDeRham.TopEdge.Intrinsic.source (IntrinsicTruncated.TruncatedModel.NativeTruncatedBase.Ring q n)
    (A.truncatedShiftModel n m hm) (A.truncatedShiftSmallCover n m hm) A.dimension

def Geometry.AbelianH1Model.truncatedShiftTopEdge : A.TruncatedShiftSmallTopForms n m hm →ₗ[IntrinsicTruncated.TruncatedModel.NativeTruncatedBase.Ring q n]
    (AlgebraicGeometry.Crystalline.Cohomology.Base.SmallDeRhamCech.BaseSmallDeRhamCech.total (IntrinsicTruncated.TruncatedModel.NativeTruncatedBase.Ring q n)
      (A.truncatedShiftModel n m hm)).homology (A.dimension + A.dimension) :=
  IntegralComparison.IntrinsicDeRham.TopEdge.Intrinsic.map (IntrinsicTruncated.TruncatedModel.NativeTruncatedBase.Ring q n)
    (A.truncatedShiftModel n m hm) (A.truncatedShiftSmallCover n m hm) A.dimension

theorem Geometry.AbelianH1Model.truncatedShiftTopEdge_surjective : Function.Surjective (A.truncatedShiftTopEdge n m hm) :=
  IntegralComparison.IntrinsicDeRham.TopEdge.Intrinsic.surjective (IntrinsicTruncated.TruncatedModel.NativeTruncatedBase.Ring q n)
    (A.truncatedShiftModel n m hm) (A.truncatedShiftSmallCover n m hm) A.dimension
    (A.truncatedShiftSmallCover_top n m hm) (A.truncatedShiftSmallCover_affine n m hm)
    (A.truncatedShiftModel_dimension_le n m hm)

def Geometry.AbelianH1Model.truncatedShiftCrystallineComparison (i : ℕ) :
    (AlgebraicGeometry.Crystalline.Cohomology.Base.SmallDeRhamCech.BaseSmallDeRhamCech.total (IntrinsicTruncated.TruncatedModel.NativeTruncatedBase.Ring q n)
      (A.truncatedShiftModel n m hm)).homology i ≃+
        A.NativeBoundedCrystallineCohomology n i :=
  IntegralComparison.TruncatedModel.IntrinsicCohomology.Intrinsic.comparisonEquiv q (ZMod q) n
    (A.truncatedShiftModel n m hm) A.specialFiber.scheme (A.truncatedShiftReduction n m hm)
    (A.truncatedShiftModel_square n m hm) (injectiveResolution _) i

def Geometry.AbelianH1Model.truncatedShiftCrystallineTopEdge : A.TruncatedShiftSmallTopForms n m hm →+
    A.NativeBoundedCrystallineCohomology n (A.dimension + A.dimension) :=
  (A.truncatedShiftCrystallineComparison n m hm (A.dimension + A.dimension)).toAddMonoidHom.comp
    (A.truncatedShiftTopEdge n m hm).toAddMonoidHom

theorem Geometry.AbelianH1Model.truncatedShiftCrystallineTopEdge_surjective :
    Function.Surjective (A.truncatedShiftCrystallineTopEdge n m hm) :=
  (A.truncatedShiftCrystallineComparison n m hm (A.dimension + A.dimension)).surjective.comp
    (A.truncatedShiftTopEdge_surjective n m hm)

end

end OAI.NumberTheory.PadicHodge.GeometricComparison

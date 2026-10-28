import OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicTruncated.TruncatedModel
import OAI.NumberTheory.PadicHodge.IntegralComparison.Smooth.ThickeningCohomologyBound

/-! # Bounds -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison

noncomputable section

/-! The original finite Witt-level models have the dimension and
Noetherian cohomology bounds of their actual special fiber. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace

variable {K : Type} [Field K] [NumberField K]
  {q : ℕ} [Fact q.Prime] {jq : K →+* ℚ_[q]} (A : Geometry.AbelianH1Model K q jq)

instance Geometry.AbelianH1Model.nativeSpecialFiber_noetherianSpace : NoetherianSpace A.specialFiber.scheme.left := by
  let : IsLocallyNoetherian A.specialFiber.scheme.left :=
    LocallyOfFiniteType.isLocallyNoetherian A.specialFiber.scheme.hom
  let : CompactSpace A.specialFiber.scheme.left :=
    QuasiCompact.compactSpace_of_compactSpace A.specialFiber.scheme.hom
  let : IsNoetherian A.specialFiber.scheme.left := {}
  infer_instance

instance Geometry.AbelianH1Model.truncatedModel_noetherianSpace (n : ℕ) :
    NoetherianSpace (A.truncatedModel n).scheme.left :=
  (noetherianSpace_iff_of_homeomorph (A.truncatedReductionHomeomorph n)).mp inferInstance

theorem Geometry.AbelianH1Model.truncatedModel_dimension_le (n : ℕ) :
    topologicalKrullDim (A.truncatedModel n).scheme.left ≤ (A.dimension : WithBot ℕ∞) :=
  IntegralComparison.Smooth.ThickeningCohomologyBound.thickening_dimension_le
    A.specialFiber.scheme A.dimension (A.truncatedReduction n)

theorem Geometry.AbelianH1Model.truncatedModel_cohomology_vanishing (n m : ℕ) (hm : A.dimension < m)
    (F : TopCat.Sheaf AddCommGrpCat (A.truncatedModel n).scheme.left.toTopCat) :
    Subsingleton (CategoryTheory.Sheaf.H F m) :=
  IntegralComparison.Smooth.ThickeningCohomologyBound.cohomology
    A.specialFiber.scheme A.dimension (A.truncatedReduction n) m hm F

end

end OAI.NumberTheory.PadicHodge.GeometricComparison

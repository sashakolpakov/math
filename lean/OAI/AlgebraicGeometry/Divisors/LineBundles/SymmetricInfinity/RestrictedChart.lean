import OAI.AlgebraicGeometry.Divisors.LineBundles.SymmetricInfinity.RestrictedEquiv
import OAI.AlgebraicGeometry.Divisors.LineBundles.Free.InfinityCharts
import OAI.AlgebraicGeometry.Divisors.LineBundles.Symmetric.BasisHyperplane
import OAI.AlgebraicGeometry.Divisors.LineBundles.Free.SymmetricProjectiveChowInjective

/-! # Restricted Chart -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.SymmetricInfinity.RestrictedChart.BundleCycles

noncomputable section

/-! On the projective spectrum of a nonzero free module, the
actual restricted infinity ideal has genuine free infinity charts. -/

open _root_.AlgebraicGeometry _root_.CategoryTheory

variable {R M ι : Type} [CommRing R] [AddCommGroup M] [Module R M] [Fintype ι]
    (basis : Module.Basis ι R M) (i : ι)

def symmetricInfinityRestriction_freeChart (x : Spec (.of R)) :
    Free.ProjectiveInfinityChart.BundleCycles.FreeProjectiveInfinityChart (SymmetricProjective.Scheme.BundleCycles.symmetricProjectiveToBase R M)
      ((Bundle.Cycles.symmetricInfinityIdealLineBundle R M).pullback (Inclusion.BundleCycles.symmetricInfinityInclusion R M)) x := by
  classical
  let N := {j : ι // j ≠ i} → R
  let e := BasisCoordinateSplit.BundleCycles.basisCoordinateSplit basis i
  exact {
    coefficient := .of R
    module := ModuleCat.of R N
    rank := Fintype.card {j : ι // j ≠ i}
    basis := (Pi.basisFun R {j : ι // j ≠ i}).reindex (Fintype.equivFin _)
    baseMap := 𝟙 _
    totalMap := (SymmetricProjective.Scheme.BundleCycles.symmetricProjectiveIso e).inv
    open_base := inferInstance
    open_total := inferInstance
    contains := ⟨x, rfl⟩
    square := IsPullback.of_vert_isIso ⟨by
      rw [Category.comp_id]
      exact (SymmetricProjective.Base.BundleCycles.symmetricProjectiveMap_over e.toLinearMap e.surjective).symm⟩
    idealIso := RestrictedEquiv.BundleCycles.symmetricInfinityRestriction_splitIso e }

theorem symmetricInfinityRestriction_freeChart_rank (x : Spec (.of R)) :
    (symmetricInfinityRestriction_freeChart basis i x).rank = Nat.card ι - 1 := by
  classical
  change Fintype.card {j : ι // j ≠ i} = Nat.card ι - 1
  exact Nat.card_eq_fintype_card.symm.trans (Free.SymmetricProjectiveChowInjective.BundleCycles.finiteBasisComplement_card i)

omit i in
include basis in
theorem symmetricInfinityRestriction_hasFreeChartsOfRank [Nonempty ι] :
    Free.InfinityCharts.BundleCycles.HasFreeProjectiveInfinityChartsOfRank (SymmetricProjective.Scheme.BundleCycles.symmetricProjectiveToBase R M)
      ((Bundle.Cycles.symmetricInfinityIdealLineBundle R M).pullback (Inclusion.BundleCycles.symmetricInfinityInclusion R M)) (Nat.card ι - 1) := by
  let i : ι := Classical.choice inferInstance
  intro x
  exact ⟨symmetricInfinityRestriction_freeChart basis i x, symmetricInfinityRestriction_freeChart_rank basis i x⟩

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.SymmetricInfinity.RestrictedChart.BundleCycles

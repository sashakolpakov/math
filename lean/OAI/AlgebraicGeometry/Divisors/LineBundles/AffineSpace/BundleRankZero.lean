import OAI.AlgebraicGeometry.Divisors.LineBundles.AffineSpaceBaseChange
import OAI.AlgebraicGeometry.Divisors.LineBundles.Relative.AffineIsomorphism

/-! # Bundle Rank Zero -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.AffineSpace.BundleRankZero.Cycles

noncomputable section

section

/-! # LineBundleCycles: actual affine-space charts of a specified relative rank -/

open _root_.AlgebraicGeometry _root_.CategoryTheory _root_.CategoryTheory.Limits

def HasAffineSpaceChartsOfRank {E X : Scheme.{0}} (p : E ⟶ X) (r : ℕ) : Prop :=
  ∀ x : X, ∃ (U : Scheme.{0}) (i : U ⟶ X) (ι : Type) (_ : Finite ι)
    (j : AffineSpace ι U ⟶ E), IsOpenImmersion i ∧ IsOpenImmersion j ∧
      x ∈ Set.range i ∧ IsPullback (AffineSpace ι U ↘ U) j i p ∧ Nat.card ι = r

theorem HasAffineSpaceChartsOfRank.forget {E X : Scheme.{0}} {p : E ⟶ X} {r : ℕ}
    (h : HasAffineSpaceChartsOfRank p r) : Affine.SpaceChartBaseChange.BundleCycles.HasAffineSpaceCharts p := by
  intro x
  obtain ⟨U, i, ι, hι, j, hi, hj, hx, hs, _⟩ := h x
  exact ⟨U, i, ι, hι, j, hi, hj, hx, hs⟩

theorem HasAffineSpaceChartsOfRank.baseChange {E X Y : Scheme.{0}} {p : E ⟶ X} {r : ℕ}
    (h : HasAffineSpaceChartsOfRank p r) (g : Y ⟶ X) :
    HasAffineSpaceChartsOfRank (pullback.snd p g) r := by
  intro y
  obtain ⟨U, i, ι, hι, j, hi, hj, hy, hs, hr⟩ := h (g y)
  let := hi
  refine ⟨pullback g i, pullback.fst g i, ι, hι,
    Affine.SpaceChartBaseChange.BundleCycles.affineSpaceChartBaseChangeMap p g i ι j hs, inferInstance, inferInstance, ?_,
    Affine.SpaceChartBaseChange.BundleCycles.affineSpaceChartBaseChange_isPullback p g i ι j hs, hr⟩
  obtain ⟨u, hu⟩ := hy
  obtain ⟨v, hv, _⟩ := Scheme.exists_preimage_of_isPullback (IsPullback.of_hasPullback g i) y u hu.symm
  exact ⟨v, hv⟩

end

/-! An actual affine-space bundle of rank zero is an isomorphism,
as follows from its cartesian affine-space charts over the base. -/

open _root_.AlgebraicGeometry _root_.CategoryTheory

theorem affineBundleRankZero_isIso {E X : Scheme.{0}} (p : E ⟶ X) (h : HasAffineSpaceChartsOfRank p 0) :
    IsIso p := by
  choose U i ι hι j hi hj hx hs hr using h
  let C : X.OpenCover := Scheme.Cover.mkOfCovers X U i (fun x => ⟨x, hx x⟩) hi
  apply Relative.AffineIsomorphism.BundleCycles.isIso_of_cover_pullbacks p C (fun x => AffineSpace (ι x) (U x)) j
    (fun x => (AffineSpace (ι x) (U x) ↘ U x)) hs
  intro x
  let := hι x
  let := Fintype.ofFinite (ι x)
  let : IsEmpty (ι x) := Fintype.card_eq_zero_iff.mp (Nat.card_eq_fintype_card.symm.trans (hr x))
  exact inferInstanceAs (IsIso (AffineSpace (ι x) (U x) ↘ U x))

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.AffineSpace.BundleRankZero.Cycles

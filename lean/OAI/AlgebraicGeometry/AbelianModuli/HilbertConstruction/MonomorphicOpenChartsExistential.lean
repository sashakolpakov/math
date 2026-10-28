import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.MonomorphicOpenChartPullback

/-! # Monomorphic Open Charts Existential -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction

noncomputable section

/-! Construct monomorphic open-chart gluing from proved existence of
the overlap lifts. Monicity identifies the selected lifts with every
specified lift having the same projection. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
universe u

variable {S : Scheme.{u}} {M : Over S} {J : Type u}
    (base : J → Over S) (baseMap : ∀ j, base j ⟶ M)
    (hopen : ∀ j, IsOpenImmersion (baseMap j).left)
    (hcovers : ∀ x : M.left, ∃ j, ∃ y : (base j).left, (baseMap j).left y = x)
    (chart : J → Over S) (chartMap : ∀ j, chart j ⟶ base j)
    (hmono : ∀ j, Mono (chartMap j))
    (hoverlap : ∀ j k, ∃ e : pullback (chartMap j ≫ baseMap j) (baseMap k) ⟶ chart k,
      e ≫ chartMap k = pullback.snd (chartMap j ≫ baseMap j) (baseMap k))

def MonomorphicOpenTo.MonomorphicOpenCharts.ofOverlapExists : MonomorphicOpenTo.MonomorphicOpenCharts M J where
  base := base
  baseMap := baseMap
  baseMap_open := hopen
  covers := hcovers
  chart := chart
  chartMap := chartMap
  chartMap_mono := hmono
  overlapLift j k := (hoverlap j k).choose
  overlapLift_map j k := (hoverlap j k).choose_spec

theorem MonomorphicOpenTo.MonomorphicOpenCharts.ofOverlapExists_overlapLift_eq (j k : J)
    (e : pullback (chartMap j ≫ baseMap j) (baseMap k) ⟶ chart k)
    (he : e ≫ chartMap k = pullback.snd (chartMap j ≫ baseMap j) (baseMap k)) :
    (MonomorphicOpenTo.MonomorphicOpenCharts.ofOverlapExists base baseMap hopen hcovers chart chartMap hmono hoverlap).overlapLift j k = e := by
  let : Mono (chartMap k) := hmono k
  apply (cancel_mono (chartMap k)).mp
  exact (hoverlap j k).choose_spec.trans he.symm

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction

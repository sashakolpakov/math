import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Chart.OverlapMaps
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Frame.Coordinates

/-! # Projective Maps -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Framed.ProjectiveMaps

noncomputable section

/-! Projective-coordinate maps defined by sections agree for any two global denominator frames. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

variable {R : Type u} [CommRing R] {X : Scheme.{u}} {L : X.Modules} {n : ℕ}

/-- Equal normalized coordinate vectors define equal projective-chart morphisms. -/
theorem projectiveChartMap_congr (c : R →+* Γ(X, ⊤))
    {v w : Fin (n + 1) → Γ(X, ⊤)} (hv : v = w) (i : Fin (n + 1))
    (hi : v i = 1) (hw : w i = 1) : ProjectiveChart.Evaluation.projectiveChartMap c v i hi = ProjectiveChart.Evaluation.projectiveChartMap c w i hw := by
  subst w
  rfl

/-- Equal coefficient maps and equal normalized coordinates define equal chart morphisms. -/
theorem projectiveChartMap_congr_coefficients {c d : R →+* Γ(X, ⊤)} (hc : c = d)
    {v w : Fin (n + 1) → Γ(X, ⊤)} (hv : v = w) (i : Fin (n + 1))
    (hi : v i = 1) (hw : w i = 1) : ProjectiveChart.Evaluation.projectiveChartMap c v i hi = ProjectiveChart.Evaluation.projectiveChartMap d w i hw := by
  subst d
  exact projectiveChartMap_congr c hv i hi hw

/-- The same family of sections gives the same map to projective space in any denominator frame. -/
theorem projectiveChartMap_frames (c : R →+* Γ(X, ⊤))
    (s : Fin (n + 1) → (Line.Bundles.structureModule X ⟶ L)) (i j : Fin (n + 1))
    [IsIso (s i)] [IsIso (s j)] :
    ProjectiveChart.Evaluation.projectiveChartMap c (fun k => Frame.Coordinates.frameCoordinate (s i) (s k)) i (Frame.Coordinates.frameCoordinate_self (s i)) =
      ProjectiveChart.Evaluation.projectiveChartMap c (fun k => Frame.Coordinates.frameCoordinate (s j) (s k)) j (Frame.Coordinates.frameCoordinate_self (s j)) := by
  have hu := Frame.Coordinates.frameCoordinate_isUnit (s i) (s j)
  let a : Γ(X, ⊤)ˣ := hu.unit
  have ha : Frame.Coordinates.frameCoordinate (s i) (s j) = a := hu.unit_spec.symm
  have hw : (fun k => (↑a⁻¹ : Γ(X, ⊤)) * Frame.Coordinates.frameCoordinate (s i) (s k)) =
      fun k => Frame.Coordinates.frameCoordinate (s j) (s k) := by
    funext k
    rw [Frame.Coordinates.frameCoordinate_change (s i) (s j) (s k), ha, ← mul_assoc, a.inv_mul, one_mul]
  exact (Chart.OverlapMaps.projectiveChartMap_normalize c (fun k => Frame.Coordinates.frameCoordinate (s i) (s k)) i j
    (Frame.Coordinates.frameCoordinate_self (s i)) a ha).trans
      (projectiveChartMap_congr c hw j _ (Frame.Coordinates.frameCoordinate_self (s j)))

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Framed.ProjectiveMaps

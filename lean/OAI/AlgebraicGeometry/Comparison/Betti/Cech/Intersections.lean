import OAI.AlgebraicGeometry.Comparison.Betti.Cech.FactorSections
import OAI.AlgebraicTopology.DeRham.Comparison.SmoothCech

/-! # Intersections -/

namespace OAI.AlgebraicGeometry.Comparison.Betti.Cech.Intersections

/-! The categorical and pointwise ordered Čech intersections are the same actual open. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.TopologicalSpace

variable {X : Type} [TopologicalSpace X] {ι : Type} (U : ι → Opens X)

theorem cechIntersection_eq_categorical {n : ℕ} (a : Fin (n + 1) → ι) :
    AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection U a = ∏ᶜ fun k : Fin (n + 1) => U (a k) := by
  apply le_antisymm
  · exact leOfHom (Pi.lift (fun k => homOfLE (AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection_le U a k)))
  · exact le_iInf (fun k => leOfHom (Pi.π (fun j : Fin (n + 1) => U (a j)) k))

end OAI.AlgebraicGeometry.Comparison.Betti.Cech.Intersections

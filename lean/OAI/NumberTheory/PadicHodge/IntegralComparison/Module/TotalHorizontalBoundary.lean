import OAI.NumberTheory.PadicHodge.IntegralComparison.Module.TotalCoordinates

/-! # Total Horizontal Boundary -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Module.TotalHorizontalBoundary

noncomputable section

/-! A vertical row cycle gives a total boundary supported only in the following row. -/

open _root_.CategoryTheory Limits

universe u v

variable {R : Type u} [CommRing R]
  (K : HomologicalComplex₂ (ModuleCat.{v} R) (.up ℕ) (.up ℕ)) [K.HasTotal (.up ℕ)]

theorem next_row (q p : ℕ) (y : (K.X q).X p) :
    (AlgebraicGeometry.SheafCohomology.Cech.UpNatLowDegrees.HomologicalComplex₂.πTotalUpNat K) (q + 1) p (q + p + 1)
      ((K.total (.up ℕ)).d (q + p) (q + p + 1)
        (K.ιTotal (.up ℕ) q p (q + p) rfl y)) = (K.d q (q + 1)).f p y := by
  have h := congrArg (fun f => f y)
    ((AlgebraicGeometry.SheafCohomology.Cech.UpNatLowDegrees.HomologicalComplex₂.ιTotal_d_upNat_assoc K) q p ((AlgebraicGeometry.SheafCohomology.Cech.UpNatLowDegrees.HomologicalComplex₂.πTotalUpNat K) (q + 1) p (q + p + 1)))
  simpa [ConcreteCategory.comp_apply] using h

theorem before_next_row (q p a b : ℕ) (ha : a < q + 1) (y : (K.X q).X p)
    (hy : (K.X q).d p (p + 1) y = 0) :
    (AlgebraicGeometry.SheafCohomology.Cech.UpNatLowDegrees.HomologicalComplex₂.πTotalUpNat K) a b (q + p + 1)
      ((K.total (.up ℕ)).d (q + p) (q + p + 1)
        (K.ιTotal (.up ℕ) q p (q + p) rfl y)) = 0 := by
  have hqa : q + 1 ≠ a := by omega
  have h := congrArg (fun f => f y)
    ((AlgebraicGeometry.SheafCohomology.Cech.UpNatLowDegrees.HomologicalComplex₂.ιTotal_d_upNat_assoc K) q p ((AlgebraicGeometry.SheafCohomology.Cech.UpNatLowDegrees.HomologicalComplex₂.πTotalUpNat K) a b (q + p + 1)))
  simpa [ConcreteCategory.comp_apply, hqa, hy, Units.smul_def] using h

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Module.TotalHorizontalBoundary

import OAI.NumberTheory.PadicHodge.IntegralComparison.Module.TotalCoordinates

/-! # Total Injection Elements -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Module.TotalInjectionElements

noncomputable section

/-! Element formulas for the original total-complex injections, before specializing the columns. -/

open _root_.CategoryTheory Limits

universe u v

variable {R : Type u} [CommRing R]
  (D : HomologicalComplex₂ (ModuleCat.{v} R) (.up ℕ) (.up ℕ)) [D.HasTotal (.up ℕ)]

theorem differential (q p n : ℕ) (hdeg : q + p = n) (x : (D.X q).X p) :
    (D.total (.up ℕ)).d n (n + 1) (D.ιTotal (.up ℕ) q p n hdeg x) =
      D.ιTotal (.up ℕ) (q + 1) p (n + 1) (by change q + 1 + p = n + 1; omega)
        ((D.d q (q + 1)).f p x) +
      ((-1 : ℤˣ) ^ q) • D.ιTotal (.up ℕ) q (p + 1) (n + 1)
        (by change q + (p + 1) = n + 1; omega) ((D.X q).d p (p + 1) x) := by
  have h := congrArg (fun a => a x) (AlgebraicGeometry.SheafCohomology.Cech.ComplexUpNatBoundary.Projective.ιTotal_d_of_sum D q p n hdeg)
  simpa [ConcreteCategory.comp_apply, Units.smul_def] using h

theorem projection_same (q p n : ℕ) (hdeg : q + p = n) (x : (D.X q).X p) :
    (AlgebraicGeometry.SheafCohomology.Cech.UpNatLowDegrees.HomologicalComplex₂.πTotalUpNat D) q p n (D.ιTotal (.up ℕ) q p n hdeg x) = x := by
  have h : D.ιTotal (.up ℕ) q p n hdeg ≫ (AlgebraicGeometry.SheafCohomology.Cech.UpNatLowDegrees.HomologicalComplex₂.πTotalUpNat D) q p n = 𝟙 ((D.X q).X p) := by
    simp [HomologicalComplex₂.XXIsoOfEq]
  exact congrArg (fun a : (D.X q).X p ⟶ (D.X q).X p => a x) h

theorem projection_other (q' p' n : ℕ) (hdeg : q' + p' = n) (q p : ℕ) (hq : q' ≠ q)
    (x : (D.X q').X p') : (AlgebraicGeometry.SheafCohomology.Cech.UpNatLowDegrees.HomologicalComplex₂.πTotalUpNat D) q p n (D.ιTotal (.up ℕ) q' p' n hdeg x) = 0 := by
  have h : D.ιTotal (.up ℕ) q' p' n hdeg ≫ (AlgebraicGeometry.SheafCohomology.Cech.UpNatLowDegrees.HomologicalComplex₂.πTotalUpNat D) q p n = 0 := by
    simp [hq]
  exact congrArg (fun a : (D.X q').X p' ⟶ (D.X q).X p => a x) h

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Module.TotalInjectionElements

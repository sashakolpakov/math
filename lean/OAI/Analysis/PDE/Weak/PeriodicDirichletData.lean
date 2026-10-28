import OAI.Analysis.PDE.Weak.PeriodicDirichletClassicalExistence

open Set Filter _root_.MeasureTheory
open scoped Topology ContDiff
noncomputable section
namespace OAI.Analysis.PDE.Weak

open OAI.Analysis.PDE.Variational

variable {m : ℕ}

theorem periodic_ae_eq_of_cell
    (J : Finset (Fin (m+1))) (a b : OAI.Analysis.PDE.Variational.CellCoordinates m)
    (hL : ∀ i ∈ J, a i < b i)
    {f g : OAI.Analysis.PDE.Variational.CellCoordinates m → ℝ}
    (hfp : ∀ z x, f (x+OAI.Analysis.PDE.Variational.coordinatePeriodShift J (b-a) z) = f x)
    (hgp : ∀ z x, g (x+OAI.Analysis.PDE.Variational.coordinatePeriodShift J (b-a) z) = g x)
    (he : f =ᵐ[volume.restrict (Icc a b)] g) :
    ∀ᵐ x, x ∈ OAI.Analysis.PDE.Variational.transverseBox J a b → f x = g x := by
  have he' : ∀ᵐ x ∂volume, x ∈ Icc a b → f x = g x :=
    (ae_restrict_iff' measurableSet_Icc).mp he
  have hall : ∀ᵐ x ∂volume, ∀ z : J → ℤ,
      x+OAI.Analysis.PDE.Variational.coordinatePeriodShift J (b-a) z ∈ Icc a b →
      f (x+OAI.Analysis.PDE.Variational.coordinatePeriodShift J (b-a) z) = g (x+OAI.Analysis.PDE.Variational.coordinatePeriodShift J (b-a) z) := by
    apply ae_all_iff.mpr
    intro z
    exact (measurePreserving_add_right volume (OAI.Analysis.PDE.Variational.coordinatePeriodShift J (b-a) z)).quasiMeasurePreserving.ae he'
  filter_upwards [hall] with x hx
  intro hxt
  obtain ⟨z,hz⟩ := OAI.Analysis.PDE.Variational.exists_translate_in_cell J a b hL x hxt
  simpa only [hfp,hgp] using hx z hz

theorem periodicRepresentative_cellToL2_ae
    (J : Finset (Fin (m+1))) (a b : OAI.Analysis.PDE.Variational.CellCoordinates m)
    (hL : ∀ i ∈ J, a i < b i)
    (g : OAI.Analysis.PDE.Variational.CellCoordinates m → ℝ) (hg : Continuous g)
    (hgp : ∀ z x, g (x+OAI.Analysis.PDE.Variational.coordinatePeriodShift J (b-a) z) = g x) :
    ∀ᵐ x, x ∈ OAI.Analysis.PDE.Variational.transverseBox J a b →
      OAI.Analysis.PDE.Variational.periodicRepresentative J a b (OAI.Analysis.PDE.Variational.cellToL2 a b g hg) x = g x := by
  apply periodic_ae_eq_of_cell J a b hL
    (OAI.Analysis.PDE.Variational.periodicRepresentative_periodic J a b hL _) hgp
  filter_upwards [OAI.Analysis.PDE.Variational.coordinateWrap_ae_eq_self J a b hL,
    (OAI.Analysis.PDE.Variational.memLp_continuous_cell a b hg).coeFn_toLp] with x hx hy
  simpa only [OAI.Analysis.PDE.Variational.periodicRepresentative,Function.comp_apply,hx,id_eq,OAI.Analysis.PDE.Variational.cellToL2] using hy

end OAI.Analysis.PDE.Weak

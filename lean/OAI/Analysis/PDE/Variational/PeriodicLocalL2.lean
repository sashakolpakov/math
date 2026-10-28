import OAI.Analysis.PDE.Variational.PeriodicRepresentative
import OAI.Analysis.PDE.Variational.ShiftedGeometry
import OAI.Analysis.PDE.Dirichlet.L2Coefficient

open Set Filter _root_.MeasureTheory
open scoped Topology ENNReal
noncomputable section
namespace OAI.Analysis.PDE.Variational

variable {m : ℕ}

def transverseInterior (J : Finset (Fin (m+1))) (a b : CellCoordinates m) :
    Set (CellCoordinates m) := {x | ∀ i, i∉J → a i<x i ∧ x i<b i}

theorem memLp_periodicRepresentative_cell {H : Type*} [NormedAddCommGroup H]
    (J : Finset (Fin (m+1))) (a b c d : CellCoordinates m)
    (hL : ∀ i∈J, a i<b i) (hlen : d-c=b-a)
    (ha : ∀ i, i∉J → c i=a i) (hb : ∀ i, i∉J → d i=b i)
    (f : Lp H 2 (volume.restrict (Icc a b))) :
    MemLp (periodicRepresentative J a b f) 2 (volume.restrict (Icc c d)) :=
  (Lp.memLp f).comp_measurePreserving (measurePreserving_coordinateWrap J a b c d hL hlen ha hb)

theorem locallyIntegrableOn_periodicRepresentative {H : Type*} [NormedAddCommGroup H]
    (J : Finset (Fin (m+1))) (a b : CellCoordinates m) (hab : a≤b)
    (hL : ∀ i∈J, a i<b i) (f : Lp H 2 (volume.restrict (Icc a b))) :
    LocallyIntegrableOn (periodicRepresentative J a b f) (transverseInterior J a b) volume := by
  intro x hx
  obtain ⟨c,d,hcd,hlen,ha,hb,hxc⟩ := exists_centered_periodic_cell J a b hab hL x hx
  let : IsFiniteMeasure (volume.restrict (Icc c d)) :=
    ⟨by simpa using (isCompact_Icc.measure_lt_top (μ := volume) : volume (Icc c d) < ⊤)⟩
  refine ⟨Icc c d, ?_, ?_⟩
  · exact nhdsWithin_le_nhds (mem_of_superset ((isOpen_cellInterior c d).mem_nhds hxc)
      (cellInterior_subset_Icc c d))
  · exact (memLp_periodicRepresentative_cell J a b c d hL hlen ha hb f).integrable (by norm_num)

theorem memLp_periodicFlux_cell
    (J : Finset (Fin (m+1))) (a b c d : CellCoordinates m)
    (hL : ∀ i∈J, a i<b i) (hlen : d-c=b-a)
    (ha : ∀ i, i∉J → c i=a i) (hb : ∀ i, i∉J → d i=b i)
    (A : CellCoordinates m → CellVectors m →L[ℝ] CellVectors m)
    (hA : AEStronglyMeasurable A (volume.restrict (Icc c d)))
    {M : ℝ} (hAM : ∀ᵐ x ∂volume.restrict (Icc c d), ‖A x‖≤M)
    (g : Lp (CellVectors m) 2 (volume.restrict (Icc a b))) :
    MemLp (fun x ↦ A x (periodicRepresentative J a b g x)) 2 (volume.restrict (Icc c d)) := by
  apply MemLp.ae_eq ?_ (OAI.Analysis.PDE.Dirichlet.coefficient_memLp A hA hAM
    (periodicCellPullback J a b c d hL hlen ha hb g))
  filter_upwards [periodicCellPullback_ae J a b c d hL hlen ha hb g] with x hx
  rw [hx]

theorem locallyIntegrableOn_periodicFlux
    (J : Finset (Fin (m+1))) (a b : CellCoordinates m) (hab : a≤b)
    (hL : ∀ i∈J, a i<b i)
    (A : CellCoordinates m → CellVectors m →L[ℝ] CellVectors m)
    (hA : AEStronglyMeasurable A volume) {M : ℝ} (hAM : ∀ᵐ x ∂volume, ‖A x‖≤M)
    (g : Lp (CellVectors m) 2 (volume.restrict (Icc a b))) :
    LocallyIntegrableOn (fun x ↦ A x (periodicRepresentative J a b g x))
      (transverseInterior J a b) volume := by
  intro x hx
  obtain ⟨c,d,hcd,hlen,ha,hb,hxc⟩ := exists_centered_periodic_cell J a b hab hL x hx
  let : IsFiniteMeasure (volume.restrict (Icc c d)) :=
    ⟨by simpa using (isCompact_Icc.measure_lt_top (μ := volume) : volume (Icc c d) < ⊤)⟩
  refine ⟨Icc c d, ?_, ?_⟩
  · exact nhdsWithin_le_nhds (mem_of_superset ((isOpen_cellInterior c d).mem_nhds hxc)
      (cellInterior_subset_Icc c d))
  · exact (memLp_periodicFlux_cell J a b c d hL hlen ha hb A hA.restrict
      (ae_restrict_of_ae hAM) g).integrable (by norm_num)

end OAI.Analysis.PDE.Variational

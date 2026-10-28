import OAI.Analysis.PDE.Energy.Rank.Energy.Comparison

noncomputable section
namespace OAI.Analysis.PDE.Energy

open Set _root_.MeasureTheory Module OAI.Analysis.Calculus.Quaternion OAI.Analysis.PDE.Dirichlet
  OAI.LinearAlgebra.Moore OAI.Analysis.PDE.Green OAI.LinearAlgebra.MixedDiscriminant
open scoped MatrixOrder ComplexOrder

/-- Rank energy comparison on a periodic cell intersected with a smooth
sublevel. Only the actual sublevel boundary has a zero Dirichlet condition. -/
theorem rank_energy_comparison_periodic_cell {n s m r : ℕ} (hn : 2 ≤ n) (hrankdim : r < n)
    (e : Fin s → Quaternion ℝ) (c : (Fin n × Fin s) ≃ Fin (m+1))
    (a b : Fin (m+1) → ℝ) (hab : a ≤ b)
    {ρ B u : OAI.Analysis.PDE.Dirichlet.CoordinateSpace n s → ℝ}
    (hB : ContDiff ℝ 3 B) (hu : ContDiff ℝ 3 u) (hρ : ContDiff ℝ 2 ρ)
    (hreg : ∀ x ∈ OAI.Analysis.PDE.Green.euclideanCoordinates c ⁻¹' Icc a b, ρ x = 0 → fderiv ℝ ρ x ≠ 0)
    (hz : ∀ x, ρ x = 0 → u x = 0) (hdata : OAI.Analysis.PDE.Green.RankCellData c a b ρ B u)
    {K : Set (OAI.Analysis.PDE.Dirichlet.CoordinateSpace n s)} (p : OAI.Analysis.PDE.Dirichlet.CoordinateSpace n s → OAI.Analysis.PDE.Dirichlet.CoordinateSpace n s)
    (hK : IsCompact K) (hKD : K ⊆ {x | ρ x ≤ 0})
    (hrep : ∀ x, ρ x ≤ 0 → p x ∈ K) (hup : ∀ x, ρ x ≤ 0 → u (p x) = u x)
    (hD : ∀ x, ρ x < 0 →
      (OAI.LinearAlgebra.Moore.complexify (OAI.Analysis.PDE.Dirichlet.quaternionHessian e (fun y => B y+u y) x)).PosDef)
    (hback : ∀ x, ρ x < 0 → (OAI.LinearAlgebra.Moore.complexify (OAI.Analysis.PDE.Dirichlet.quaternionHessian e B x)).PosSemidef)
    (hrank : ∀ x, ρ x < 0 → OAI.LinearAlgebra.Moore.QuaternionRankLE r (OAI.Analysis.PDE.Dirichlet.quaternionHessian e B x))
    {Λ : ℝ} (hΛ : 0 < Λ) :
    let S := (OAI.Analysis.PDE.Green.euclideanCoordinates c ⁻¹' Icc a b) ∩ {x | ρ x < 0}
    let X := determinantMass e S (fun y => B y+u y) u / Λ
    let E := (determinantMass e S (fun y => B y+u y) u + determinantSegmentEnergy e S B u) / Λ
    ((n : ℝ)-r)/((n : ℝ)+1)*X ≤ E ∧ E ≤ (n : ℝ)/((n : ℝ)+1)*X := by
  let S := (OAI.Analysis.PDE.Green.euclideanCoordinates c ⁻¹' Icc a b) ∩ {x | ρ x < 0}
  have hS : MeasurableSet S :=
    ((isClosed_Icc.preimage (OAI.Analysis.PDE.Green.euclideanCoordinates c).continuous).measurableSet).inter
      (isOpen_lt hρ.continuous continuous_const).measurableSet
  have hb : Bornology.IsBounded S := (OAI.Analysis.PDE.Green.isBounded_euclidean_cell c a b).subset inter_subset_left
  have hneg := correction_nonpos_rank_representatives hrankdim e p hK hKD hρ.continuous
    (hB.of_le (by norm_num)) (hu.of_le (by norm_num)) hrep hup hD hback hrank hz
  have hDS : ∀ x ∈ S,
      (OAI.LinearAlgebra.Moore.complexify (OAI.Analysis.PDE.Dirichlet.quaternionHessian e (fun y => B y+u y) x)).PosSemidef :=
    fun x hx => (hD x hx.2).posSemidef
  have hBS : ∀ x ∈ S, (OAI.LinearAlgebra.Moore.complexify (OAI.Analysis.PDE.Dirichlet.quaternionHessian e B x)).PosSemidef :=
    fun x hx => hback x hx.2
  apply rank_energy_comparison_of_mixed_moments hrankdim e hS hb hB hu
  · exact fun j _ => mixedHessianMass_nonneg e hS (fun x hx => hneg x hx.2.le) hBS hDS j
  · exact fun j hj => OAI.LinearAlgebra.MixedDiscriminant.mixedHessianMass_succ_le_cell (by omega) e c a b hab hB hu hρ hreg hz hdata
      hDS hBS j hj
  · exact fun j hrj hjn => mixedHessianMass_eq_zero_of_rank e hS hBS hDS
      (fun x hx => hrank x hx.2) hrj hjn
  · exact hΛ

/-- The compact representative hypotheses are supplied by a genuine lattice
quotient with bounded transverse closure. -/
theorem rank_energy_comparison_lattice_cell {P V ι : Type*}
    [NormedAddCommGroup P] [NormedSpace ℝ P]
    [NormedAddCommGroup V] [NormedSpace ℝ V] [Fintype ι]
    {n s m r : ℕ} (hn : 2 ≤ n) (hrankdim : r < n)
    (slots : Fin s → Quaternion ℝ) (c : (Fin n × Fin s) ≃ Fin (m+1))
    (a b : Fin (m+1) → ℝ) (hab : a ≤ b)
    (e : OAI.Analysis.PDE.Dirichlet.CoordinateSpace n s ≃L[ℝ] P × V) (basis : Basis ι ℝ P)
    {C : Set V} (hC : IsCompact C) {ρ B u : OAI.Analysis.PDE.Dirichlet.CoordinateSpace n s → ℝ}
    (hB : ContDiff ℝ 3 B) (hu : ContDiff ℝ 3 u) (hρ : ContDiff ℝ 2 ρ)
    (hreg : ∀ x ∈ OAI.Analysis.PDE.Green.euclideanCoordinates c ⁻¹' Icc a b, ρ x = 0 → fderiv ℝ ρ x ≠ 0)
    (hz : ∀ x, ρ x = 0 → u x = 0) (hdata : OAI.Analysis.PDE.Green.RankCellData c a b ρ B u)
    (hbounded : ∀ x, ρ x ≤ 0 → (e x).2 ∈ C)
    (hρper : OAI.Analysis.PDE.Dirichlet.LatticePeriodic e basis ρ) (huper : OAI.Analysis.PDE.Dirichlet.LatticePeriodic e basis u)
    (hD : ∀ x, ρ x < 0 →
      (OAI.LinearAlgebra.Moore.complexify (OAI.Analysis.PDE.Dirichlet.quaternionHessian slots (fun y => B y+u y) x)).PosDef)
    (hback : ∀ x, ρ x < 0 → (OAI.LinearAlgebra.Moore.complexify (OAI.Analysis.PDE.Dirichlet.quaternionHessian slots B x)).PosSemidef)
    (hrank : ∀ x, ρ x < 0 → OAI.LinearAlgebra.Moore.QuaternionRankLE r (OAI.Analysis.PDE.Dirichlet.quaternionHessian slots B x))
    {Λ : ℝ} (hΛ : 0 < Λ) :
    let S := (OAI.Analysis.PDE.Green.euclideanCoordinates c ⁻¹' Icc a b) ∩ {x | ρ x < 0}
    let X := determinantMass slots S (fun y => B y+u y) u / Λ
    let E := (determinantMass slots S (fun y => B y+u y) u + determinantSegmentEnergy slots S B u) / Λ
    ((n : ℝ)-r)/((n : ℝ)+1)*X ≤ E ∧ E ≤ (n : ℝ)/((n : ℝ)+1)*X := by
  exact rank_energy_comparison_periodic_cell hn hrankdim slots c a b hab hB hu hρ hreg hz hdata
    (OAI.Analysis.PDE.Dirichlet.latticeRepresentative e basis) (OAI.Analysis.PDE.Dirichlet.isCompact_latticeSublevelCell e basis hC hρ.continuous)
    inter_subset_right (fun x hx => OAI.Analysis.PDE.Dirichlet.latticeRepresentative_mem_sublevelCell e basis hρper hbounded hx)
    (fun x _ => huper.representative x) hD hback hrank hΛ

end OAI.Analysis.PDE.Energy

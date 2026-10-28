import OAI.Analysis.PDE.Green.Physical.LocalizedCutoff

/-! A finite time box and one spatial period, in the source's actual physical
coordinates. Its spatial fibers lie in the uniform cutoff box. -/

noncomputable section
namespace OAI.Analysis.PDE.Green

open Set _root_.MeasureTheory OAI.Analysis.PDE.Dirichlet

def physicalTimeBoxLower {d m : ℕ}
    (c : (Fin (d + 2) × Fin 3) ≃ Fin (m + 1)) (L : ℝ) (j : Fin (m + 1)) : ℝ :=
  if (c.symm j).1 = 0 then -L else if (c.symm j).2 = 0 then 0 else -29

def physicalTimeBoxUpper {d m : ℕ}
    (c : (Fin (d + 2) × Fin 3) ≃ Fin (m + 1)) (L : ℝ) (j : Fin (m + 1)) : ℝ :=
  if (c.symm j).1 = 0 then L else if (c.symm j).2 = 0 then 1 else 29

theorem physicalTimeBoxLower_le_upper {d m : ℕ}
    (c : (Fin (d + 2) × Fin 3) ≃ Fin (m + 1)) {L : ℝ} (hL : 0 ≤ L) :
    physicalTimeBoxLower c L ≤ physicalTimeBoxUpper c L := by
  intro j
  simp only [physicalTimeBoxLower, physicalTimeBoxUpper]
  split_ifs <;> linarith

theorem fiberEmbedding_apply_zero {n s : ℕ} (z : OAI.Analysis.PDE.Dirichlet.CoordinateSpace 1 s)
    (y : OAI.Analysis.PDE.Dirichlet.CoordinateSpace n s) (j : Fin s) :
    fiberEmbedding n s z y (0, j) = z (0, j) := by
  simp [fiberEmbedding, timeInjection, spatialInjection, spatialInjectionLinear]

theorem fiberEmbedding_apply_succ {n s : ℕ} (z : OAI.Analysis.PDE.Dirichlet.CoordinateSpace 1 s)
    (y : OAI.Analysis.PDE.Dirichlet.CoordinateSpace n s) (i : Fin n) (j : Fin s) :
    fiberEmbedding n s z y (i.succ, j) = y (i, j) := by
  simp [fiberEmbedding, timeInjection, spatialInjection, spatialInjectionLinear]

theorem physicalTimeBox_fiber_subset {d m k : ℕ}
    (c : (Fin (d + 2) × Fin 3) ≃ Fin (m + 1))
    (b : (Fin (d + 1) × Fin 3) ≃ Fin (k + 1)) (L : ℝ) (z : OAI.Analysis.PDE.Dirichlet.CoordinateSpace 1 3) :
    (fiberEmbedding (d + 1) 3 z) ⁻¹'
      (euclideanCoordinates c ⁻¹' Icc (physicalTimeBoxLower c L) (physicalTimeBoxUpper c L)) ⊆
    euclideanCoordinates b ⁻¹' Icc (physicalBoxLower (physicalOptionCoordinates b))
      (physicalBoxUpper (physicalOptionCoordinates b)) := by
  intro y hy
  constructor
  · intro j
    have h := hy.1 (c ((b.symm j).1.succ, (b.symm j).2))
    simpa only [physicalTimeBoxLower, Equiv.symm_apply_apply, Fin.succ_ne_zero, ite_false,
      physical_euclideanCoordinates_apply, fiberEmbedding_apply_succ,
      physicalBoxLower, physicalOptionCoordinates_slot, Prod.mk.eta] using! h
  · intro j
    have h := hy.2 (c ((b.symm j).1.succ, (b.symm j).2))
    simpa only [physicalTimeBoxUpper, Equiv.symm_apply_apply, Fin.succ_ne_zero, ite_false,
      physical_euclideanCoordinates_apply, fiberEmbedding_apply_succ,
      physicalBoxUpper, physicalOptionCoordinates_slot, Prod.mk.eta] using! h

theorem physicalTimeBox_fiber_eq {d m k : ℕ}
    (c : (Fin (d + 2) × Fin 3) ≃ Fin (m + 1))
    (b : (Fin (d + 1) × Fin 3) ≃ Fin (k + 1)) (L : ℝ) (z : OAI.Analysis.PDE.Dirichlet.CoordinateSpace 1 3)
    (hz : ∀ j : Fin 3, -L ≤ z (0, j) ∧ z (0, j) ≤ L) :
    (fiberEmbedding (d + 1) 3 z) ⁻¹'
      (euclideanCoordinates c ⁻¹' Icc (physicalTimeBoxLower c L) (physicalTimeBoxUpper c L)) =
    euclideanCoordinates b ⁻¹' Icc (physicalBoxLower (physicalOptionCoordinates b))
      (physicalBoxUpper (physicalOptionCoordinates b)) := by
  apply Subset.antisymm (physicalTimeBox_fiber_subset c b L z)
  intro y hy
  constructor
  · intro j
    obtain ⟨⟨i, s⟩, rfl⟩ := c.surjective j
    refine Fin.cases ?_ (fun i => ?_) i
    · simpa only [physicalTimeBoxLower, Equiv.symm_apply_apply, ite_true,
        physical_euclideanCoordinates_apply, fiberEmbedding_apply_zero] using (hz s).1
    · have h := hy.1 (b (i, s))
      simpa only [physicalTimeBoxLower, physicalBoxLower, physicalOptionCoordinates_slot,
        Equiv.symm_apply_apply, Fin.succ_ne_zero, ite_false, physical_euclideanCoordinates_apply,
        fiberEmbedding_apply_succ] using h
  · intro j
    obtain ⟨⟨i, s⟩, rfl⟩ := c.surjective j
    refine Fin.cases ?_ (fun i => ?_) i
    · simpa only [physicalTimeBoxUpper, Equiv.symm_apply_apply, ite_true,
        physical_euclideanCoordinates_apply, fiberEmbedding_apply_zero] using (hz s).2
    · have h := hy.2 (b (i, s))
      simpa only [physicalTimeBoxUpper, physicalBoxUpper, physicalOptionCoordinates_slot,
        Equiv.symm_apply_apply, Fin.succ_ne_zero, ite_false, physical_euclideanCoordinates_apply,
        fiberEmbedding_apply_succ] using h

theorem physicalTimeBox_sublevel_fiber_eq {d m k : ℕ}
    (c : (Fin (d + 2) × Fin 3) ≃ Fin (m + 1))
    (b : (Fin (d + 1) × Fin 3) ≃ Fin (k + 1)) (L a : ℝ) (ha : 0 < a)
    (z : OAI.Analysis.PDE.Dirichlet.CoordinateSpace 1 3) (ht : a ≤ ‖energyComplexTime z‖) (ht' : ‖energyComplexTime z‖ ≤ 4)
    (hz : ∀ j : Fin 3, -L ≤ z (0, j) ∧ z (0, j) ≤ L)
    (R : (ℂ × (Option (Fin d) → ℂ)) → ℝ)
    (hneg : ∀ q, R (energyComplexTime z, q) < 0 ↔
      OAI.Analysis.Calculus.Current.physicalFiberDefining (1 / 10) a (energyComplexTime z) q < 0) :
    (fiberEmbedding (d + 1) 3 z) ⁻¹'
      ((euclideanCoordinates c ⁻¹' Icc (physicalTimeBoxLower c L) (physicalTimeBoxUpper c L)) ∩
        {x | R (fullPhysicalProjection d x) < 0}) =
      physicalSpatialFiber d a (energyComplexTime z) := by
  rw [Set.preimage_inter, physicalTimeBox_fiber_eq c b L z hz]
  rw [physicalSpatialFiber_eq_cell b a (energyComplexTime z) ha ht ht' hneg]
  congr 1
  ext y
  simp only [Set.mem_preimage, Set.mem_ofPred_eq, fullPhysicalProjection_fiber]

theorem physicalTimeBox_energy_eq {d m k : ℕ}
    (c : (Fin (d + 2) × Fin 3) ≃ Fin (m + 1))
    (b : (Fin (d + 1) × Fin 3) ≃ Fin (k + 1)) (L a : ℝ) (ha : 0 < a)
    (z : OAI.Analysis.PDE.Dirichlet.CoordinateSpace 1 3) (ht : a ≤ ‖energyComplexTime z‖) (ht' : ‖energyComplexTime z‖ ≤ 4)
    (hz : ∀ j : Fin 3, -L ≤ z (0, j) ∧ z (0, j) ≤ L)
    (R : (ℂ × (Option (Fin d) → ℂ)) → ℝ)
    (hneg : ∀ q, R (energyComplexTime z, q) < 0 ↔
      OAI.Analysis.Calculus.Current.physicalFiberDefining (1 / 10) a (energyComplexTime z) q < 0)
    (e : Fin 3 → Quaternion ℝ) (lam : ℝ)
    (A : OAI.Analysis.PDE.Dirichlet.CoordinateSpace (d + 2) 3 → Matrix (Fin (d + 2)) (Fin (d + 2)) (Quaternion ℝ))
    (B u : OAI.Analysis.PDE.Dirichlet.CoordinateSpace (d + 2) 3 → ℝ) :
    setFiberCombinedEnergy e lam
      ((euclideanCoordinates c ⁻¹' Icc (physicalTimeBoxLower c L) (physicalTimeBoxUpper c L)) ∩
        {x | R (fullPhysicalProjection d x) < 0}) A B u z =
    setFiberCombinedEnergy e lam (physicalEnergyCell d a) A B u z := by
  unfold setFiberCombinedEnergy
  rw [physicalEnergyCell_fiber, physicalTimeBox_sublevel_fiber_eq c b L a ha z ht ht' hz R hneg]

end OAI.Analysis.PDE.Green

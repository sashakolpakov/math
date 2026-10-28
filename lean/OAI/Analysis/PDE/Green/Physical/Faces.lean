import OAI.Analysis.PDE.Green.Physical.TimeSupport

/-! Coordinate facts for cancellation of the auxiliary finite-box faces. -/

noncomputable section
namespace OAI.Analysis.PDE.Green

open Set Filter _root_.MeasureTheory OAI.Analysis.PDE.Dirichlet
open scoped Topology

theorem fullPhysicalProjection_spatial_coordinate_norm {d : ℕ}
    (x : OAI.Analysis.PDE.Dirichlet.CoordinateSpace (d + 2) 3) (i : Fin (d + 1)) (j : Fin 3) (hj : j ≠ 0) :
    ‖x (i.succ, j)‖ ≤ ‖(fullPhysicalProjection d x).2‖ := by
  let q := (fullPhysicalProjection d x).2 (finSuccEquiv d i)
  have hr : q.re = x (i.succ, 1) := by simp [q, fullPhysicalProjection]
  have hi : q.im = x (i.succ, 2) := by simp [q, fullPhysicalProjection]
  have hb : ‖q‖ ≤ ‖(fullPhysicalProjection d x).2‖ := by
    exact norm_le_pi_norm ((fullPhysicalProjection d x).2) (finSuccEquiv d i)
  fin_cases j
  · exact (hj rfl).elim
  · change ‖x (i.succ, 1)‖ ≤ ‖(fullPhysicalProjection d x).2‖
    rw [← hr, Real.norm_eq_abs]
    exact (Complex.abs_re_le_norm q).trans hb
  · change ‖x (i.succ, 2)‖ ≤ ‖(fullPhysicalProjection d x).2‖
    rw [← hi, Real.norm_eq_abs]
    exact (Complex.abs_im_le_norm q).trans hb

theorem physical_face_coordinate {d m : ℕ}
    (c : (Fin (d + 2) × Fin 3) ≃ Fin (m + 1))
    (i : Fin (m + 1)) (y : Fin m → ℝ) (t : ℝ) :
    (euclideanCoordinates c).symm (i.insertNth t y) (c.symm i) = t := by
  have h := physical_euclideanCoordinates_apply c
    ((euclideanCoordinates c).symm (i.insertNth t y)) i
  simpa only [ContinuousLinearEquiv.apply_symm_apply, Fin.insertNth_apply_same] using h.symm

theorem euclideanCoordinates_symm_single_scalar
    {ι : Type*} [Fintype ι] [DecidableEq ι] {m : ℕ} (c : ι ≃ Fin (m + 1))
    (i : Fin (m + 1)) (t : ℝ) :
    (euclideanCoordinates c).symm (Pi.single i t) = t • EuclideanSpace.single (c.symm i) 1 := by
  have h : (Pi.single i t : Fin (m + 1) → ℝ) = t • Pi.single i 1 := by
    ext j
    simp [Pi.single_apply]
  rw [h, map_smul, euclideanCoordinates_symm_single]

theorem physical_spatial_faces_time_eq {d m : ℕ}
    (c : (Fin (d + 2) × Fin 3) ≃ Fin (m + 1))
    (i : Fin (m + 1)) (y : Fin m → ℝ) (a b : ℝ)
    (j : Fin (d + 1)) (s : Fin 3) (hci : c.symm i = (j.succ, s)) :
    timeProjection (d + 1) 3 ((euclideanCoordinates c).symm (i.insertNth b y)) =
      timeProjection (d + 1) 3 ((euclideanCoordinates c).symm (i.insertNth a y)) := by
  rw [insertNth_eq_add_single, map_add, euclideanCoordinates_symm_single_scalar, map_add,
    map_smul, hci]
  change _ + (b - a) • timeProjection (d + 1) 3 (OAI.Analysis.PDE.Dirichlet.coordinateVector (j.succ, s)) = _
  rw [timeProjection_coordinate_succ, smul_zero, add_zero]

theorem physical_time_face_notMem_tsupport {d m : ℕ}
    (c : (Fin (d + 2) × Fin 3) ≃ Fin (m + 1))
    (i : Fin (m + 1)) (y : Fin m → ℝ) (s : Fin 3) (hci : c.symm i = (0, s))
    {η : OAI.Analysis.PDE.Dirichlet.CoordinateSpace 1 3 → ℝ} {L : ℝ}
    (hL : ∀ z ∈ tsupport η, -L < z (0, s) ∧ z (0, s) < L) :
    timeProjection (d + 1) 3 ((euclideanCoordinates c).symm (i.insertNth L y)) ∉ tsupport η ∧
      timeProjection (d + 1) 3 ((euclideanCoordinates c).symm (i.insertNth (-L) y)) ∉ tsupport η := by
  have hp (t : ℝ) :
      timeProjection (d + 1) 3 ((euclideanCoordinates c).symm (i.insertNth t y)) (0, s) = t := by
    change (euclideanCoordinates c).symm (i.insertNth t y) (0, s) = t
    rw [← hci]
    exact physical_face_coordinate c i y t
  constructor
  · intro h
    have hh := (hL _ h).2
    rw [hp] at hh
    exact (lt_irrefl _ hh)
  · intro h
    have hh := (hL _ h).1
    rw [hp] at hh
    exact (lt_irrefl _ hh)

/-- Real spatial faces cancel by periodicity; imaginary faces lie outside the
fiber; time faces lie outside the test support. -/
theorem physical_time_box_compatible_faces {d m : ℕ}
    (c : (Fin (d + 2) × Fin 3) ≃ Fin (m + 1)) (L : ℝ)
    (R : (ℂ × (Option (Fin d) → ℂ)) → ℝ) (η : OAI.Analysis.PDE.Dirichlet.CoordinateSpace 1 3 → ℝ)
    (hL : ∀ z ∈ tsupport η, ∀ s, -L < z (0, s) ∧ z (0, s) < L)
    (hbounded : ∀ x, timeProjection (d + 1) 3 x ∈ tsupport η →
      R (fullPhysicalProjection d x) ≤ 0 → ‖(fullPhysicalProjection d x).2‖ ≤ 28)
    (F : (Fin (d + 2) × Fin 3) → OAI.Analysis.PDE.Dirichlet.CoordinateSpace (d + 2) 3 → ℝ)
    (hperiod : ∀ p (j : Fin (d + 1)) x, F p (x + OAI.Analysis.PDE.Dirichlet.coordinateVector (j.succ, 0)) = F p x)
    (hzero : ∀ x, timeProjection (d + 1) 3 x ∉ tsupport η → ∀ p, F p x = 0) :
    CompatibleCellFaces c (physicalTimeBoxLower c L) (physicalTimeBoxUpper c L)
      (fun x => R (fullPhysicalProjection d x)) F := by
  intro i y hy
  by_cases hi : (c.symm i).1 = 0
  · apply Or.inr ∘ Or.inr
    have hci : c.symm i = (0, (c.symm i).2) := Prod.ext hi rfl
    have hz := physical_time_face_notMem_tsupport c i y (c.symm i).2 hci
      (fun z hz => hL z hz (c.symm i).2)
    constructor
    · simpa only [physicalTimeBoxUpper, hi, ite_true] using hzero _ hz.1 (c.symm i)
    · simpa only [physicalTimeBoxLower, hi, ite_true] using hzero _ hz.2 (c.symm i)
  · obtain ⟨j, hj⟩ := Fin.exists_succ_eq_of_ne_zero hi
    have hci : c.symm i = (j.succ, (c.symm i).2) := Prod.ext hj.symm rfl
    let xu := (euclideanCoordinates c).symm (i.insertNth (physicalTimeBoxUpper c L i) y)
    let xl := (euclideanCoordinates c).symm (i.insertNth (physicalTimeBoxLower c L i) y)
    have ht : timeProjection (d + 1) 3 xu = timeProjection (d + 1) 3 xl :=
      physical_spatial_faces_time_eq c i y _ _ j _ hci
    by_cases hs : (c.symm i).2 = 0
    · have hc0 : c.symm i = (j.succ, 0) := hci.trans (Prod.ext rfl hs)
      have hd : physicalTimeBoxUpper c L i - physicalTimeBoxLower c L i = 1 := by
        simp [physicalTimeBoxUpper, physicalTimeBoxLower, hi, hs]
      have hxeq : xu = xl + OAI.Analysis.PDE.Dirichlet.coordinateVector (j.succ, 0) := by
        dsimp only [xu, xl]
        rw [insertNth_eq_add_single, hd, map_add, euclideanCoordinates_symm_single, hc0]
        rfl
      apply Or.inl
      change R (fullPhysicalProjection d xu) = R (fullPhysicalProjection d xl) ∧
        F (c.symm i) xu = F (c.symm i) xl
      rw [hxeq, fullPhysicalProjection_real_translation, hperiod]
      exact ⟨rfl, rfl⟩
    · by_cases hz : timeProjection (d + 1) 3 xu ∈ tsupport η
      · apply Or.inr ∘ Or.inl
        change 0 ≤ R (fullPhysicalProjection d xu) ∧ 0 ≤ R (fullPhysicalProjection d xl)
        have hxl : timeProjection (d + 1) 3 xl ∈ tsupport η := ht ▸ hz
        have hcu : xu (j.succ, (c.symm i).2) = 29 := by
          have h := physical_face_coordinate c i y (physicalTimeBoxUpper c L i)
          change xu (c.symm i) = physicalTimeBoxUpper c L i at h
          have h' : xu (c.symm i) = 29 := by
            simpa only [physicalTimeBoxUpper, hi, hs, ite_false] using h
          rw [hci] at h'
          exact h'
        have hcl : xl (j.succ, (c.symm i).2) = -29 := by
          have h := physical_face_coordinate c i y (physicalTimeBoxLower c L i)
          change xl (c.symm i) = physicalTimeBoxLower c L i at h
          have h' : xl (c.symm i) = -29 := by
            simpa only [physicalTimeBoxLower, hi, hs, ite_false] using h
          rw [hci] at h'
          exact h'
        constructor
        · by_contra hn
          have hb := hbounded xu hz (le_of_lt (lt_of_not_ge hn))
          have hc := fullPhysicalProjection_spatial_coordinate_norm xu j _ hs
          rw [hcu] at hc
          norm_num at hc
          linarith
        · by_contra hn
          have hb := hbounded xl hxl (le_of_lt (lt_of_not_ge hn))
          have hc := fullPhysicalProjection_spatial_coordinate_norm xl j _ hs
          rw [hcl] at hc
          norm_num at hc
          linarith
      · apply Or.inr ∘ Or.inr
        exact ⟨hzero xu hz _, hzero xl (fun h => hz (ht.symm ▸ h)) _⟩

end OAI.Analysis.PDE.Green

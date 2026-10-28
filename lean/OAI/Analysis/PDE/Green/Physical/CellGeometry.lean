import OAI.Analysis.PDE.Green.Physical.Fubini
import OAI.Analysis.PDE.Green.Physical.Cutoff
import OAI.Analysis.PDE.Green.Periodicity

/-! The actual physical fiber as a regular sublevel in a rectangular periodic
cell. The rational defining function is replaced only outside its closed
sublevel; no boundary chart or defining-function regularity is assumed. -/

noncomputable section
namespace OAI.Analysis.PDE.Green

open Set Filter _root_.MeasureTheory OAI.Analysis.Calculus.Current OAI.Analysis.Calculus.Quaternion OAI.Analysis.PDE.Dirichlet
open scoped Topology ContDiff

def physicalSpatialProjection (d : ℕ) :
    OAI.Analysis.PDE.Dirichlet.CoordinateSpace (d + 1) 3 →L[ℝ] (Option (Fin d) → ℂ) :=
  ContinuousLinearMap.pi fun i =>
    Complex.ofRealCLM.comp (EuclideanSpace.proj ((finSuccEquiv d).symm i, 1)) +
      Complex.I • Complex.ofRealCLM.comp
        (EuclideanSpace.proj ((finSuccEquiv d).symm i, 2))

theorem physicalSpatialProjection_apply (d : ℕ) (y : OAI.Analysis.PDE.Dirichlet.CoordinateSpace (d + 1) 3)
    (i : Option (Fin d)) :
    physicalSpatialProjection d y i =
      (y ((finSuccEquiv d).symm i, 1) : ℂ) +
        Complex.I * (y ((finSuccEquiv d).symm i, 2) : ℂ) := rfl

theorem physicalSpatialProjection_embedding (d : ℕ) (x : Fin (d + 1) → ℝ)
    (q : Option (Fin d) → ℂ) :
    physicalSpatialProjection d (physicalSpatialEmbedding d x q) = q := by
  ext i
  simp [physicalSpatialProjection_apply, physicalSpatialEmbedding_eq,
    spatialRealComplexEmbedding_apply, Complex.ext_iff]

theorem physicalSpatialProjection_eq (d : ℕ) (y : OAI.Analysis.PDE.Dirichlet.CoordinateSpace (d + 1) 3) :
    physicalSpatialProjection d y = (physicalSpatialEquiv d y).2 := by
  have h := physicalSpatialProjection_embedding d (physicalSpatialEquiv d y).1
    (physicalSpatialEquiv d y).2
  simpa only [physicalSpatialEmbedding, Prod.mk.eta,
    MeasurableEquiv.symm_apply_apply] using h

theorem physicalSpatialEquiv_fst (d : ℕ) (y : OAI.Analysis.PDE.Dirichlet.CoordinateSpace (d + 1) 3)
    (i : Fin (d + 1)) : (physicalSpatialEquiv d y).1 i = y (i, 0) := by
  have h : physicalSpatialEmbedding d (physicalSpatialEquiv d y).1
      (physicalSpatialEquiv d y).2 = y :=
    (physicalSpatialEquiv d).symm_apply_apply y
  have hi := congrArg (fun z : OAI.Analysis.PDE.Dirichlet.CoordinateSpace (d + 1) 3 => z (i, 0)) h
  simpa only [physicalSpatialEmbedding_eq, spatialRealComplexEmbedding_apply,
    Matrix.cons_val_zero] using hi

def physicalOptionCoordinates {d m : ℕ}
    (c : (Fin (d + 1) × Fin 3) ≃ Fin (m + 1)) :
    (Option (Fin d) × Fin 3) ≃ Fin (m + 1) :=
  (Equiv.prodCongr (finSuccEquiv d).symm (Equiv.refl (Fin 3))).trans c

theorem physical_euclideanCoordinates_apply {d m : ℕ}
    (c : (Fin (d + 1) × Fin 3) ≃ Fin (m + 1))
    (x : OAI.Analysis.PDE.Dirichlet.CoordinateSpace (d + 1) 3) (j : Fin (m + 1)) :
    euclideanCoordinates c x j = x (c.symm j) := by
  obtain ⟨i, rfl⟩ := c.surjective j
  simp [euclideanCoordinates, ContinuousLinearEquiv.piCongrLeft,
    Equiv.piCongrLeft_apply_apply]

theorem complexSpatialProjection_euclidean {d m : ℕ}
    (c : (Fin (d + 1) × Fin 3) ≃ Fin (m + 1))
    (x : OAI.Analysis.PDE.Dirichlet.CoordinateSpace (d + 1) 3) :
    complexSpatialProjection (physicalOptionCoordinates c) (euclideanCoordinates c x) =
      physicalSpatialProjection d x := by
  ext i
  simp [complexSpatialProjection_apply, physicalSpatialProjection_apply,
    physicalOptionCoordinates, physical_euclideanCoordinates_apply]

theorem physicalOptionCoordinates_slot {d m : ℕ}
    (c : (Fin (d + 1) × Fin 3) ≃ Fin (m + 1)) (j : Fin (m + 1)) :
    ((physicalOptionCoordinates c).symm j).2 = (c.symm j).2 := rfl

theorem physicalSpatialFiber_eq_cell {d m : ℕ}
    (c : (Fin (d + 1) × Fin 3) ≃ Fin (m + 1))
    (a : ℝ) (τ : ℂ) (ha : 0 < a) (ht : a ≤ ‖τ‖) (ht' : ‖τ‖ ≤ 4)
    {R : (Option (Fin d) → ℂ) → ℝ}
    (hneg : ∀ q, R q < 0 ↔ OAI.Analysis.Calculus.Current.physicalFiberDefining (1 / 10) a τ q < 0) :
    physicalSpatialFiber d a τ =
      (euclideanCoordinates c ⁻¹'
        Icc (physicalBoxLower (physicalOptionCoordinates c))
          (physicalBoxUpper (physicalOptionCoordinates c))) ∩
        {y | R (physicalSpatialProjection d y) < 0} := by
  ext y
  change ((physicalSpatialEquiv d y).1 ∈ Icc 0 1 ∧
      OAI.Analysis.Calculus.Current.physicalFiberDefining (1 / 10) a τ (physicalSpatialEquiv d y).2 < 0) ↔ _
  rw [← physicalSpatialProjection_eq]
  constructor
  · rintro ⟨hX, hq⟩
    refine ⟨?_, (hneg _).mpr hq⟩
    have hb : ‖physicalSpatialProjection d y‖ ≤ 28 := by
      have hh := OAI.Analysis.Calculus.Current.physical_fiber_collar_norm_bound a τ (physicalSpatialProjection d y)
        ha ht (hq.le.trans (by norm_num))
      linarith
    constructor
    · intro j
      by_cases hj : (c.symm j).2 = 0
      · have hci : c.symm j = ((c.symm j).1, 0) := Prod.ext rfl hj
        simp only [physicalBoxLower, physicalOptionCoordinates_slot, hj, ite_true,
          physical_euclideanCoordinates_apply]
        rw [hci]
        simpa only [physicalSpatialEquiv_fst, Pi.zero_apply] using hX.1 (c.symm j).1
      · have hh := abs_coordinate_le_complexProjection_norm
          (physicalOptionCoordinates c) (euclideanCoordinates c y) j hj
        rw [complexSpatialProjection_euclidean] at hh
        have hl := (abs_le.mp ((Real.norm_eq_abs _ ▸ hh).trans hb)).1
        simpa [physicalBoxLower, physicalOptionCoordinates_slot, hj] using
          (show (-29 : ℝ) ≤ euclideanCoordinates c y j by linarith)
    · intro j
      by_cases hj : (c.symm j).2 = 0
      · have hci : c.symm j = ((c.symm j).1, 0) := Prod.ext rfl hj
        simp only [physicalBoxUpper, physicalOptionCoordinates_slot, hj, ite_true,
          physical_euclideanCoordinates_apply]
        rw [hci]
        simpa only [physicalSpatialEquiv_fst, Pi.one_apply] using hX.2 (c.symm j).1
      · have hh := abs_coordinate_le_complexProjection_norm
          (physicalOptionCoordinates c) (euclideanCoordinates c y) j hj
        rw [complexSpatialProjection_euclidean] at hh
        have hl := (abs_le.mp ((Real.norm_eq_abs _ ▸ hh).trans hb)).2
        simpa [physicalBoxUpper, physicalOptionCoordinates_slot, hj] using
          (show euclideanCoordinates c y j ≤ (29 : ℝ) by linarith)
  · rintro ⟨hbox, hr⟩
    refine ⟨⟨?_, ?_⟩, (hneg _).mp hr⟩
    · intro i
      have h := hbox.1 (c (i, 0))
      simpa [physicalBoxLower, physicalOptionCoordinates_slot, physicalSpatialEquiv_fst,
        physical_euclideanCoordinates_apply] using h
    · intro i
      have h := hbox.2 (c (i, 0))
      simpa [physicalBoxUpper, physicalOptionCoordinates_slot, physicalSpatialEquiv_fst,
        physical_euclideanCoordinates_apply] using h

/-- A smooth defining function for the actual fiber with regular zero level.
It agrees with the rational defining function near the entire closed fiber. -/
theorem exists_physical_spatial_defining (d : ℕ) (a : ℝ) (τ : ℂ)
    (ha : 0 < a) (ht : a ≤ ‖τ‖) (ht' : ‖τ‖ ≤ 4) :
    ∃ R : (Option (Fin d) → ℂ) → ℝ,
      ContDiff ℝ 3 R ∧
      (∀ q, R q < 0 ↔ OAI.Analysis.Calculus.Current.physicalFiberDefining (1 / 10) a τ q < 0) ∧
      (∀ q, R q = 0 ↔ OAI.Analysis.Calculus.Current.physicalFiberDefining (1 / 10) a τ q = 0) ∧
      (∀ q, R q ≤ 0 → ‖q‖ ≤ 28) ∧
      (∀ y, R (physicalSpatialProjection d y) = 0 →
        fderiv ℝ (fun v => R (physicalSpatialProjection d v)) y ≠ 0) := by
  obtain ⟨C, hC, hgeom⟩ := exists_physical_bounded_extensions d
  obtain ⟨R, V, hR, hV, heq, hneg, hnonpos, hbound⟩ := hgeom a τ ha ht ht'
  refine ⟨R, hR, hneg, ?_, fun q hq => (hbound q hq).2.2.2, ?_⟩
  · intro q
    constructor
    · intro hq
      have hq' := (hnonpos q).mp hq.le
      exact (heq q hq').1.eq_of_nhds.symm.trans hq
    · intro hq
      exact (heq q hq.le).1.eq_of_nhds.trans hq
  · intro y hy hz
    let q := physicalSpatialProjection d y
    have htrans := (hbound q hy.le).1
    have hd : fderiv ℝ (fun v => R (physicalSpatialProjection d v)) y =
        (fderiv ℝ R q).comp (physicalSpatialProjection d) :=
      (((hR.differentiable (by norm_num) q).hasFDerivAt).comp y
        (physicalSpatialProjection d).hasFDerivAt).fderiv
    have h := congrArg
      (fun L : OAI.Analysis.PDE.Dirichlet.CoordinateSpace (d + 1) 3 →L[ℝ] ℝ =>
        L (physicalSpatialEmbedding d 0 (V q))) (hd.symm.trans hz)
    simp only [ContinuousLinearMap.comp_apply, physicalSpatialProjection_embedding,
      zero_apply] at h
    change 1 ≤ fderiv ℝ R q (V q) + (R q) ^ 2 at htrans
    change R q = 0 at hy
    rw [h, hy] at htrans
    norm_num at htrans

/-- Real periodicity supplies the artificial faces; the imaginary faces lie
outside the actual fiber. -/
theorem physical_cell_compatible_faces {d m : ℕ}
    (c : (Fin (d + 1) × Fin 3) ≃ Fin (m + 1))
    (R : (Option (Fin d) → ℂ) → ℝ)
    (hbounded : ∀ q, R q ≤ 0 → ‖q‖ ≤ 28)
    (F : (Fin (d + 1) × Fin 3) → OAI.Analysis.PDE.Dirichlet.CoordinateSpace (d + 1) 3 → ℝ)
    (hperiod : ∀ p j x, F p (x + OAI.Analysis.PDE.Dirichlet.coordinateVector (j, 0)) = F p x) :
    CompatibleCellFaces c (physicalBoxLower (physicalOptionCoordinates c))
      (physicalBoxUpper (physicalOptionCoordinates c))
      (fun x => R (physicalSpatialProjection d x)) F := by
  intro i y hy
  let e := euclideanCoordinates c
  let cp := physicalOptionCoordinates c
  by_cases hi : (c.symm i).2 = 0
  · apply Or.inl
    constructor
    · simp only [← complexSpatialProjection_euclidean c, ContinuousLinearEquiv.apply_symm_apply]
      apply congrArg R
      simpa only [Fin.update_insertNth] using
        complexSpatialProjection_update_real cp
          (i.insertNth (physicalBoxLower cp i) y) i (physicalBoxUpper cp i) hi
    · have hdiff : physicalBoxUpper cp i - physicalBoxLower cp i = 1 := by
        simp [cp, physicalBoxUpper, physicalBoxLower, physicalOptionCoordinates_slot, hi]
      have hci : c.symm i = ((c.symm i).1, 0) := Prod.ext rfl hi
      rw [insertNth_eq_add_single, hdiff, map_add, euclideanCoordinates_symm_single, hci]
      exact hperiod _ _ _
  · apply Or.inr ∘ Or.inl
    constructor
    · by_contra hn
      have hb := hbounded _ (le_of_lt (lt_of_not_ge hn))
      have hc := abs_coordinate_le_complexProjection_norm cp
        (i.insertNth (physicalBoxUpper cp i) y) i hi
      have hp := complexSpatialProjection_euclidean c
        (e.symm (i.insertNth (physicalBoxUpper cp i) y))
      simp only [e, ContinuousLinearEquiv.apply_symm_apply] at hp
      rw [hp] at hc
      simp only [Fin.insertNth_apply_same, cp, physicalBoxUpper,
        physicalOptionCoordinates_slot, hi, ite_false, Real.norm_eq_abs,
        abs_of_nonneg (show (0 : ℝ) ≤ 29 by norm_num)] at hc
      simp only [physicalBoxUpper, physicalOptionCoordinates_slot, hi, ite_false] at hb
      linarith
    · by_contra hn
      have hb := hbounded _ (le_of_lt (lt_of_not_ge hn))
      have hc := abs_coordinate_le_complexProjection_norm cp
        (i.insertNth (physicalBoxLower cp i) y) i hi
      have hp := complexSpatialProjection_euclidean c
        (e.symm (i.insertNth (physicalBoxLower cp i) y))
      simp only [e, ContinuousLinearEquiv.apply_symm_apply] at hp
      rw [hp] at hc
      simp only [Fin.insertNth_apply_same, cp, physicalBoxLower,
        physicalOptionCoordinates_slot, hi, ite_false, Real.norm_eq_abs, abs_neg,
        abs_of_nonneg (show (0 : ℝ) ≤ 29 by norm_num)] at hc
      simp only [physicalBoxLower, physicalOptionCoordinates_slot, hi, ite_false] at hb
      linarith

end OAI.Analysis.PDE.Green

import OAI.Analysis.PDE.Concentration.Lattice.Propagation
import OAI.Analysis.PDE.Concentration.Physical.LatticeFaces
import OAI.Analysis.PDE.Concentration.Lattice.EnergyCell
import OAI.Analysis.PDE.Green.Physical.Propagation

noncomputable section
namespace OAI.Analysis.PDE.Concentration

open Set Filter Matrix _root_.MeasureTheory OAI.Analysis.PDE.Energy OAI.Analysis.PDE.Green OAI.Analysis.Calculus.Current OAI.Analysis.Calculus.Quaternion OAI.Analysis.PDE.Dirichlet OAI.LinearAlgebra.Moore
open scoped Topology Matrix.Norms.Elementwise MatrixOrder ComplexOrder

theorem physical_lattice_combined_energy_weak_bound {d m k : ℕ}
    (c : (Fin (d + 2) × Fin 3) ≃ Fin (m + 1))
    (b : (Fin (d + 1) × Fin 3) ≃ Fin (k + 1))
    (R₀ : OAI.Analysis.Calculus.Current.SpatialSpace d ≃L[ℝ] OAI.Analysis.Calculus.Current.SpatialSpace d)
    (e : Fin 3 → Quaternion ℝ)
    (he : ∀ α β, (e α * star (e β)).re = if α = β then 1 else 0)
    (a : ℝ) (ha : 0 < a)
    {A : OAI.Analysis.PDE.Dirichlet.CoordinateSpace (d + 2) 3 → Matrix (Fin (d + 2)) (Fin (d + 2)) (Quaternion ℝ)}
    (hA : ContDiff ℝ 1 A) (hAh : ∀ x, (A x).IsHermitian)
    (hAp : ∀ (j : Fin (d + 1)) x, A (x + physicalCellPeriod c R₀ j) = A x)
    (hdiv : ∀ x ∈ OAI.Analysis.PDE.Green.physicalPropagationDomain d a, ∀ j,
      OAI.Analysis.Calculus.Quaternion.strongDivergence e (fun p => fderiv ℝ A x (OAI.Analysis.PDE.Dirichlet.coordinateVector p)) j = 0)
    {B u : OAI.Analysis.PDE.Dirichlet.CoordinateSpace (d + 2) 3 → ℝ}
    (hB : ContDiff ℝ 3 B) (hu : ContDiff ℝ 3 u)
    (hBp : ∀ (j : Fin (d + 1)) x, B (x + physicalCellPeriod c R₀ j) = B x)
    (hup : ∀ (j : Fin (d + 1)) x, u (x + physicalCellPeriod c R₀ j) = u x)
    (hcommon : ∀ x, (a < ‖(OAI.Analysis.PDE.Green.fullPhysicalProjection d x).1‖ ∧ ‖(OAI.Analysis.PDE.Green.fullPhysicalProjection d x).1‖ < 4) →
      OAI.Analysis.PDE.Green.physicalFullDefining d a x = 0 → ∃ w : Fin (d + 2) → Quaternion ℝ, w ≠ 0 ∧
        OAI.Analysis.PDE.Dirichlet.quaternionHessian e (OAI.Analysis.PDE.Green.physicalFullDefining d a) x *ᵥ w = 0 ∧
        OAI.Analysis.PDE.Dirichlet.quaternionHessian e B x *ᵥ w = 0 ∧
        star (OAI.Analysis.PDE.Dirichlet.quaternionGradient e (OAI.Analysis.PDE.Green.physicalFullDefining d a) x) ⬝ᵥ w = 0)
    {lam : ℝ} (hlam : 0 < lam)
    (hApos : ∀ x ∈ OAI.Analysis.PDE.Green.physicalPropagationDomain d a, (OAI.LinearAlgebra.Moore.complexify (A x)).PosSemidef)
    (hBpos : ∀ x ∈ OAI.Analysis.PDE.Green.physicalPropagationDomain d a,
      (OAI.LinearAlgebra.Moore.complexify ((OAI.Analysis.PDE.Dirichlet.quaternionHessian e B x).submatrix Fin.succ Fin.succ)).PosSemidef)
    (hDpos : ∀ x ∈ OAI.Analysis.PDE.Green.physicalPropagationDomain d a,
      (OAI.LinearAlgebra.Moore.complexify ((OAI.Analysis.PDE.Dirichlet.quaternionHessian e (fun y => B y + u y) x).submatrix Fin.succ Fin.succ)).PosDef)
    (hequation : ∀ x ∈ OAI.Analysis.PDE.Green.physicalPropagationDomain d a,
      OAI.LinearAlgebra.Moore.mooreDet (d + 1) ((OAI.Analysis.PDE.Dirichlet.quaternionHessian e (fun y => B y + u y) x).submatrix Fin.succ Fin.succ) =
        lam * (A x 0 0).re)
    (hann : ∀ x ∈ OAI.Analysis.PDE.Green.physicalPropagationDomain d a, OAI.LinearAlgebra.Moore.realTrace (A x * OAI.Analysis.PDE.Dirichlet.quaternionHessian e B x) = 0)
    (hBdet : ∀ x ∈ OAI.Analysis.PDE.Green.physicalPropagationDomain d a, OAI.LinearAlgebra.Moore.mooreDet (d + 2) (OAI.Analysis.PDE.Dirichlet.quaternionHessian e B x) = 0)
    {ε G : ℝ} (hε : 0 ≤ ε) (hG : 0 ≤ G)
    (hboundary : ∀ x, (a < ‖(OAI.Analysis.PDE.Green.fullPhysicalProjection d x).1‖ ∧ ‖(OAI.Analysis.PDE.Green.fullPhysicalProjection d x).1‖ < 4) →
      OAI.Analysis.PDE.Green.physicalFullDefining d a x = 0 → u x = 0 ∧
        ‖star (OAI.Analysis.PDE.Dirichlet.quaternionGradient e (OAI.Analysis.PDE.Green.physicalFullDefining d a) x) ᵥ* A x‖ ≤ ε ∧
        ‖OAI.Analysis.PDE.Dirichlet.quaternionGradient e u x‖ ≤ G)
    {η : OAI.Analysis.PDE.Dirichlet.CoordinateSpace 1 3 → ℝ} (hη : ContDiff ℝ 3 η) (hηs : HasCompactSupport η)
    (hηpos : ∀ z, 0 ≤ η z)
    (hηann : ∀ z ∈ tsupport η, a < ‖OAI.Analysis.PDE.Green.energyComplexTime z‖ ∧ ‖OAI.Analysis.PDE.Green.energyComplexTime z‖ < 4) :
    (∫ z, Laplacian.laplacian η z * OAI.Analysis.PDE.Green.setFiberCombinedEnergy e lam (physicalLatticeEnergyCell R₀ a) A B u z) ≤
      |(physicalCellLatticeMap c R₀).toLinearEquiv.toLinearMap.det| *
        ((d + 2 : ℕ) * ε * G * OAI.Analysis.PDE.Green.physicalCutoffConstant b * ∫ z, η z) := by
  let T := OAI.Analysis.PDE.Green.energyComplexTime '' tsupport η
  have hT : IsCompact T := hηs.image (by unfold OAI.Analysis.PDE.Green.energyComplexTime; fun_prop)
  have hTann : ∀ τ ∈ T, a < ‖τ‖ ∧ ‖τ‖ < 4 := by
    rintro τ ⟨z, hz, rfl⟩
    exact hηann z hz
  obtain ⟨R, hR, hReq, hRneg, hRnonpos, hRreg⟩ :=
    OAI.Analysis.PDE.Green.exists_physical_joint_regular_extension (d := d) a ha hT (fun τ hτ => (hTann τ hτ).1.le)
  obtain ⟨L, hL, hLs⟩ := OAI.Analysis.PDE.Green.exists_time_test_box hηs
  let lo := OAI.Analysis.PDE.Green.physicalTimeBoxLower c L
  let hi := OAI.Analysis.PDE.Green.physicalTimeBoxUpper c L
  let r := fun x => R (OAI.Analysis.PDE.Green.fullPhysicalProjection d x)
  let S := euclideanLatticeCell c (physicalCellLatticeMap c R₀) lo hi ∩ {x | r x < 0}
  have hr : ContDiff ℝ 2 r := (hR.of_le (by norm_num)).comp (OAI.Analysis.PDE.Green.fullPhysicalProjection d).contDiff
  have hbox : MeasurableSet (OAI.Analysis.PDE.Green.euclideanCoordinates c ⁻¹' Icc lo hi) :=
    (isClosed_Icc.preimage (OAI.Analysis.PDE.Green.euclideanCoordinates c).continuous).measurableSet
  have hTmem (x : OAI.Analysis.PDE.Dirichlet.CoordinateSpace (d + 2) 3)
      (hx : OAI.Analysis.PDE.Green.timeProjection (d + 1) 3 x ∈ tsupport η) : (OAI.Analysis.PDE.Green.fullPhysicalProjection d x).1 ∈ T := by
    rw [OAI.Analysis.PDE.Green.fullPhysicalProjection_fst]
    exact mem_image_of_mem OAI.Analysis.PDE.Green.energyComplexTime hx
  have hactive (x : OAI.Analysis.PDE.Dirichlet.CoordinateSpace (d + 2) 3) (hx : x ∈ S)
      (hz : OAI.Analysis.PDE.Green.timeProjection (d + 1) 3 x ∈ tsupport η) : x ∈ OAI.Analysis.PDE.Green.physicalPropagationDomain d a := by
    exact ⟨hTann _ (hTmem x hz), (hRneg _ (hTmem x hz) _).mp hx.2⟩
  have hbound (x : OAI.Analysis.PDE.Dirichlet.CoordinateSpace (d + 2) 3)
      (hz : OAI.Analysis.PDE.Green.timeProjection (d + 1) 3 x ∈ tsupport η) (hx : r x ≤ 0) :
      ‖(OAI.Analysis.PDE.Green.fullPhysicalProjection d x).2‖ ≤ 28 := by
    have ht := hTann _ (hTmem x hz)
    have hraw := (hRnonpos _ (hTmem x hz) _).mp hx
    have hh := OAI.Analysis.Calculus.Current.physical_fiber_collar_norm_bound a (OAI.Analysis.PDE.Green.fullPhysicalProjection d x).1
      (OAI.Analysis.PDE.Green.fullPhysicalProjection d x).2 ha ht.1.le (hraw.trans (by norm_num))
    linarith
  have hboundary' (x : OAI.Analysis.PDE.Dirichlet.CoordinateSpace (d + 2) 3)
      (hxT : (OAI.Analysis.PDE.Green.fullPhysicalProjection d x).1 ∈ T) (hx : r x = 0) :
      ∀ᶠ y in 𝓝 x, r y = 0 → u y = 0 ∧
        ‖star (OAI.Analysis.PDE.Dirichlet.quaternionGradient e r y) ᵥ* A y‖ ≤ ε ∧ ‖OAI.Analysis.PDE.Dirichlet.quaternionGradient e u y‖ ≤ G :=
    OAI.Analysis.PDE.Green.physical_extension_local_boundary_data a R hReq hRnonpos hTann e A u ε G hboundary hxT hx
  have hreg (x : OAI.Analysis.PDE.Dirichlet.CoordinateSpace (d + 2) 3) (hx : r x = 0) :
      fderiv ℝ r x ≠ 0 ∨ (fun y => η (OAI.Analysis.PDE.Green.timeProjection (d + 1) 3 y)) =ᶠ[𝓝 x] (fun _ => 0) :=
    OAI.Analysis.PDE.Green.fullPhysical_extension_regular_or_test_zero (hR.of_le (by norm_num)) (Subset.refl T) hRreg x hx
  have hcommon' (x : OAI.Analysis.PDE.Dirichlet.CoordinateSpace (d + 2) 3) (hx : r x = 0) :
      ((∀ᶠ y in 𝓝 x, r y = 0 → u y = 0) ∧
        ∃ w : Fin (d + 2) → Quaternion ℝ, w ≠ 0 ∧ OAI.Analysis.PDE.Dirichlet.quaternionHessian e r x *ᵥ w = 0 ∧
          OAI.Analysis.PDE.Dirichlet.quaternionHessian e B x *ᵥ w = 0 ∧ star (OAI.Analysis.PDE.Dirichlet.quaternionGradient e r x) ⬝ᵥ w = 0) ∨
      (fun y => η (OAI.Analysis.PDE.Green.timeProjection (d + 1) 3 y)) =ᶠ[𝓝 x] (fun _ => 0) := by
    by_cases hxT : (OAI.Analysis.PDE.Green.fullPhysicalProjection d x).1 ∈ T
    · refine Or.inl ⟨(hboundary' x hxT hx).mono (fun y hy hy0 => (hy hy0).1), ?_⟩
      apply OAI.Analysis.PDE.Green.physical_extension_common_kernel a R hReq hRnonpos e B hxT hx
      exact hcommon x (hTann _ hxT)
        ((OAI.Analysis.PDE.Green.physical_extension_boundary_germ a R hReq hRnonpos hxT hx).eq_of_nhds.symm.trans hx)
    · exact Or.inr (OAI.Analysis.PDE.Green.time_test_eventually_zero_of_notMem (Subset.refl T) hxT)
  have hdiv' (x : OAI.Analysis.PDE.Dirichlet.CoordinateSpace (d + 2) 3) (hx : x ∈ S) :
      (∀ j, OAI.Analysis.Calculus.Quaternion.strongDivergence e (fun p => fderiv ℝ A x (OAI.Analysis.PDE.Dirichlet.coordinateVector p)) j = 0) ∨
      (fun y => η (OAI.Analysis.PDE.Green.timeProjection (d + 1) 3 y)) =ᶠ[𝓝 x] (fun _ => 0) := by
    by_cases hz : OAI.Analysis.PDE.Green.timeProjection (d + 1) 3 x ∈ tsupport η
    · exact Or.inl (hdiv x (hactive x hx hz))
    · exact Or.inr (OAI.Analysis.PDE.Green.time_test_zero_off_tsupport hz)
  have hWbase : ∀ j : ℕ, (∫ x in OAI.Analysis.PDE.Green.euclideanCoordinates c ⁻¹' Icc lo hi,
      OAI.Analysis.PDE.Green.normalCutoffWeight (r x) j * ‖η (OAI.Analysis.PDE.Green.timeProjection (d + 1) 3 x)‖) ≤
      OAI.Analysis.PDE.Green.physicalCutoffConstant b * ∫ z, ‖η z‖ :=
    (Classical.choose_spec (OAI.Analysis.PDE.Green.exists_uniform_physical_weighted_cutoff_bound b)).2
      a ha T (fun τ hτ => ⟨(hTann τ hτ).1.le, (hTann τ hτ).2.le⟩)
      R hR.continuous hReq hRneg _ hbox (OAI.Analysis.PDE.Green.isBounded_euclidean_cell c lo hi)
      (OAI.Analysis.PDE.Green.physicalTimeBox_fiber_subset c b L) η hη.continuous
      (hη.continuous.integrable_of_hasCompactSupport hηs) (Subset.refl T)
  have hW : ∀ j : ℕ, (∫ x in Icc lo hi,
      OAI.Analysis.PDE.Green.normalCutoffWeight (r ((OAI.Analysis.PDE.Green.euclideanCoordinates c).symm (physicalCellLatticeMap c R₀ x))) j *
        ‖η (OAI.Analysis.PDE.Green.timeProjection (d + 1) 3 ((OAI.Analysis.PDE.Green.euclideanCoordinates c).symm (physicalCellLatticeMap c R₀ x)))‖) ≤
      OAI.Analysis.PDE.Green.physicalCutoffConstant b * ∫ z, ‖η z‖ := by
    intro j
    simp_rw [r, physicalCellLatticeMap_cutoff_weight]
    have heq := (OAI.Analysis.PDE.Green.measurePreserving_euclideanCoordinates c).setIntegral_preimage_emb
      (OAI.Analysis.PDE.Green.euclideanCoordinates c).toHomeomorph.measurableEmbedding
      (fun y => OAI.Analysis.PDE.Green.normalCutoffWeight (r ((OAI.Analysis.PDE.Green.euclideanCoordinates c).symm y)) j *
        ‖η (OAI.Analysis.PDE.Green.timeProjection (d + 1) 3 ((OAI.Analysis.PDE.Green.euclideanCoordinates c).symm y))‖) (Icc lo hi)
    simp only [ContinuousLinearEquiv.symm_apply_apply] at heq
    rw [← heq]
    exact hWbase j
  have hfaceA : CompatibleLatticeFaces c (physicalCellLatticeMap c R₀) lo hi r (OAI.Analysis.PDE.Green.secondGreenFlux OAI.Analysis.PDE.Dirichlet.coordinateVector
      (fun p q x => OAI.Analysis.Calculus.Quaternion.realCoefficients e (A x) p q) u (fun x => η (OAI.Analysis.PDE.Green.timeProjection (d + 1) 3 x))) := by
    apply physical_lattice_secondGreen_faces c R₀ L R η hLs hbound _ u _ hup
    intro p q j x
    rw [hAp j x]
  have hfaceC := physical_lattice_cofactor_faces c R₀ L R η hLs hbound e B u hBp hup
  have hweak := combined_fiber_energy_lattice_weak_bound e he c (physicalCellLatticeMap c R₀) lo hi
    (OAI.Analysis.PDE.Green.physicalTimeBoxLower_le_upper c hL.le) hA hAh hdiv' hr hB hu hη hηpos
    (fun x _ hx => hreg x hx) hcommon' hlam
    (fun x hx hz => hApos x (hactive x hx (subset_tsupport η hz)))
    (fun x hx hz => hDpos x (hactive x hx (subset_tsupport η hz)))
    (fun x hx hz => hequation x (hactive x hx (subset_tsupport η hz)))
    (fun x hx hz => hann x (hactive x hx (subset_tsupport η hz)))
    (fun x hx hz => hBdet x (hactive x hx (subset_tsupport η hz)))
    (fun x hx hz t ht => OAI.Analysis.PDE.Green.spatial_hessian_segment_posSemidef e
      (hB.of_le (by norm_num)) (hu.of_le (by norm_num)) x
      (hBpos x (hactive x hx (OAI.Analysis.PDE.Green.laplacian_nonzero_mem_tsupport hz)))
      (hDpos x (hactive x hx (OAI.Analysis.PDE.Green.laplacian_nonzero_mem_tsupport hz))).posSemidef ht)
    hε hG hW
    (fun x _ hx => by
      by_cases hxT : (OAI.Analysis.PDE.Green.fullPhysicalProjection d x).1 ∈ T
      · exact Or.inl ⟨OAI.Analysis.PDE.Green.fullPhysical_extension_regular (hR.of_le (by norm_num))
          (hRreg _ hxT _ hx), hboundary' x hxT hx⟩
      · exact Or.inr (OAI.Analysis.PDE.Green.time_test_eventually_zero_of_notMem (Subset.refl T) hxT))
    hfaceA hfaceC
  have heq := physicalLatticeTimeBox_weak_energy_eq c b R₀ L a ha η
    (fun z hz => ⟨(hηann z hz).1.le, (hηann z hz).2.le⟩)
    (fun z hz j => ⟨(hLs z hz j).1.le, (hLs z hz j).2.le⟩) R
    (fun z hz q => hRneg _ (mem_image_of_mem OAI.Analysis.PDE.Green.energyComplexTime hz) q) e lam A B u
  change (∫ z, Laplacian.laplacian η z * OAI.Analysis.PDE.Green.setFiberCombinedEnergy e lam
    (euclideanLatticeCell c (physicalCellLatticeMap c R₀) lo hi ∩ {x | r x < 0}) A B u z) ≤
      |(physicalCellLatticeMap c R₀).toLinearEquiv.toLinearMap.det| *
        ((d + 2 : ℕ) * ε * G * (OAI.Analysis.PDE.Green.physicalCutoffConstant b * ∫ z, ‖η z‖)) at hweak
  rw [heq] at hweak
  simpa only [Real.norm_eq_abs, abs_of_nonneg (hηpos _), mul_assoc] using hweak


end OAI.Analysis.PDE.Concentration

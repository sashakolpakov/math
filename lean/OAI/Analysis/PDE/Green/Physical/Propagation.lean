import OAI.Analysis.PDE.Green.Localized.Propagation
import OAI.Analysis.PDE.Green.Physical.FluxFaces
import OAI.Analysis.PDE.Green.Physical.BoundaryTransfer
import OAI.Analysis.PDE.Green.Physical.JointExtension

/-! Weak propagation on the source's actual moving fibers. All artificial
boxes, cutoff masses, defining-function extensions, and face cancellations
are constructed here. The remaining inputs are the actual current/PDE and
boundary conditions, not an assumed energy or Laplacian estimate. -/

noncomputable section
namespace OAI.Analysis.PDE.Green

open Set Filter Matrix _root_.MeasureTheory OAI.Analysis.Calculus.Current OAI.Analysis.Calculus.Quaternion OAI.Analysis.PDE.Dirichlet OAI.LinearAlgebra.Moore
open scoped Topology Matrix.Norms.Elementwise MatrixOrder ComplexOrder

def physicalCutoffConstant {d k : ℕ} (c : (Fin (d + 1) × Fin 3) ≃ Fin (k + 1)) : ℝ :=
  Classical.choose (exists_uniform_physical_weighted_cutoff_bound c)

theorem physicalCutoffConstant_nonneg {d k : ℕ}
    (c : (Fin (d + 1) × Fin 3) ≃ Fin (k + 1)) : 0 ≤ physicalCutoffConstant c :=
  (Classical.choose_spec (exists_uniform_physical_weighted_cutoff_bound c)).1

def physicalPropagationDomain (d : ℕ) (a : ℝ) : Set (OAI.Analysis.PDE.Dirichlet.CoordinateSpace (d + 2) 3) :=
  {x | (a < ‖(fullPhysicalProjection d x).1‖ ∧ ‖(fullPhysicalProjection d x).1‖ < 4) ∧
    physicalFullDefining d a x < 0}

theorem physical_combined_energy_weak_bound {d m k : ℕ}
    (c : (Fin (d + 2) × Fin 3) ≃ Fin (m + 1))
    (b : (Fin (d + 1) × Fin 3) ≃ Fin (k + 1))
    (e : Fin 3 → Quaternion ℝ)
    (he : ∀ α β, (e α * star (e β)).re = if α = β then 1 else 0)
    (a : ℝ) (ha : 0 < a)
    {A : OAI.Analysis.PDE.Dirichlet.CoordinateSpace (d + 2) 3 → Matrix (Fin (d + 2)) (Fin (d + 2)) (Quaternion ℝ)}
    (hA : ContDiff ℝ 1 A) (hAh : ∀ x, (A x).IsHermitian)
    (hAp : ∀ (j : Fin (d + 1)) x, A (x + OAI.Analysis.PDE.Dirichlet.coordinateVector (j.succ, 0)) = A x)
    (hdiv : ∀ x ∈ physicalPropagationDomain d a, ∀ j,
      OAI.Analysis.Calculus.Quaternion.strongDivergence e (fun p => fderiv ℝ A x (OAI.Analysis.PDE.Dirichlet.coordinateVector p)) j = 0)
    {B u : OAI.Analysis.PDE.Dirichlet.CoordinateSpace (d + 2) 3 → ℝ}
    (hB : ContDiff ℝ 3 B) (hu : ContDiff ℝ 3 u)
    (hBp : ∀ (j : Fin (d + 1)) x, B (x + OAI.Analysis.PDE.Dirichlet.coordinateVector (j.succ, 0)) = B x)
    (hup : ∀ (j : Fin (d + 1)) x, u (x + OAI.Analysis.PDE.Dirichlet.coordinateVector (j.succ, 0)) = u x)
    (hcommon : ∀ x, (a < ‖(fullPhysicalProjection d x).1‖ ∧ ‖(fullPhysicalProjection d x).1‖ < 4) →
      physicalFullDefining d a x = 0 → ∃ w : Fin (d + 2) → Quaternion ℝ, w ≠ 0 ∧
        OAI.Analysis.PDE.Dirichlet.quaternionHessian e (physicalFullDefining d a) x *ᵥ w = 0 ∧
        OAI.Analysis.PDE.Dirichlet.quaternionHessian e B x *ᵥ w = 0 ∧
        star (OAI.Analysis.PDE.Dirichlet.quaternionGradient e (physicalFullDefining d a) x) ⬝ᵥ w = 0)
    {lam : ℝ} (hlam : 0 < lam)
    (hApos : ∀ x ∈ physicalPropagationDomain d a, (OAI.LinearAlgebra.Moore.complexify (A x)).PosSemidef)
    (hBpos : ∀ x ∈ physicalPropagationDomain d a,
      (OAI.LinearAlgebra.Moore.complexify ((OAI.Analysis.PDE.Dirichlet.quaternionHessian e B x).submatrix Fin.succ Fin.succ)).PosSemidef)
    (hDpos : ∀ x ∈ physicalPropagationDomain d a,
      (OAI.LinearAlgebra.Moore.complexify ((OAI.Analysis.PDE.Dirichlet.quaternionHessian e (fun y => B y + u y) x).submatrix Fin.succ Fin.succ)).PosDef)
    (hequation : ∀ x ∈ physicalPropagationDomain d a,
      OAI.LinearAlgebra.Moore.mooreDet (d + 1) ((OAI.Analysis.PDE.Dirichlet.quaternionHessian e (fun y => B y + u y) x).submatrix Fin.succ Fin.succ) =
        lam * (A x 0 0).re)
    (hann : ∀ x ∈ physicalPropagationDomain d a, OAI.LinearAlgebra.Moore.realTrace (A x * OAI.Analysis.PDE.Dirichlet.quaternionHessian e B x) = 0)
    (hBdet : ∀ x ∈ physicalPropagationDomain d a, OAI.LinearAlgebra.Moore.mooreDet (d + 2) (OAI.Analysis.PDE.Dirichlet.quaternionHessian e B x) = 0)
    {ε G : ℝ} (hε : 0 ≤ ε) (hG : 0 ≤ G)
    (hboundary : ∀ x, (a < ‖(fullPhysicalProjection d x).1‖ ∧ ‖(fullPhysicalProjection d x).1‖ < 4) →
      physicalFullDefining d a x = 0 → u x = 0 ∧
        ‖star (OAI.Analysis.PDE.Dirichlet.quaternionGradient e (physicalFullDefining d a) x) ᵥ* A x‖ ≤ ε ∧
        ‖OAI.Analysis.PDE.Dirichlet.quaternionGradient e u x‖ ≤ G)
    {η : OAI.Analysis.PDE.Dirichlet.CoordinateSpace 1 3 → ℝ} (hη : ContDiff ℝ 3 η) (hηs : HasCompactSupport η)
    (hηpos : ∀ z, 0 ≤ η z)
    (hηann : ∀ z ∈ tsupport η, a < ‖energyComplexTime z‖ ∧ ‖energyComplexTime z‖ < 4) :
    (∫ z, Laplacian.laplacian η z * setFiberCombinedEnergy e lam (physicalEnergyCell d a) A B u z) ≤
      (d + 2 : ℕ) * ε * G * physicalCutoffConstant b * ∫ z, η z := by
  let T := energyComplexTime '' tsupport η
  have hT : IsCompact T := hηs.image (by unfold energyComplexTime; fun_prop)
  have hTann : ∀ τ ∈ T, a < ‖τ‖ ∧ ‖τ‖ < 4 := by
    rintro τ ⟨z, hz, rfl⟩
    exact hηann z hz
  obtain ⟨R, hR, hReq, hRneg, hRnonpos, hRreg⟩ :=
    exists_physical_joint_regular_extension (d := d) a ha hT (fun τ hτ => (hTann τ hτ).1.le)
  obtain ⟨L, hL, hLs⟩ := exists_time_test_box hηs
  let lo := physicalTimeBoxLower c L
  let hi := physicalTimeBoxUpper c L
  let r := fun x => R (fullPhysicalProjection d x)
  let S := (euclideanCoordinates c ⁻¹' Icc lo hi) ∩ {x | r x < 0}
  have hr : ContDiff ℝ 2 r := (hR.of_le (by norm_num)).comp (fullPhysicalProjection d).contDiff
  have hbox : MeasurableSet (euclideanCoordinates c ⁻¹' Icc lo hi) :=
    (isClosed_Icc.preimage (euclideanCoordinates c).continuous).measurableSet
  have hTmem (x : OAI.Analysis.PDE.Dirichlet.CoordinateSpace (d + 2) 3)
      (hx : timeProjection (d + 1) 3 x ∈ tsupport η) : (fullPhysicalProjection d x).1 ∈ T := by
    rw [fullPhysicalProjection_fst]
    exact mem_image_of_mem energyComplexTime hx
  have hactive (x : OAI.Analysis.PDE.Dirichlet.CoordinateSpace (d + 2) 3) (hx : x ∈ S)
      (hz : timeProjection (d + 1) 3 x ∈ tsupport η) : x ∈ physicalPropagationDomain d a := by
    exact ⟨hTann _ (hTmem x hz), (hRneg _ (hTmem x hz) _).mp hx.2⟩
  have hbound (x : OAI.Analysis.PDE.Dirichlet.CoordinateSpace (d + 2) 3)
      (hz : timeProjection (d + 1) 3 x ∈ tsupport η) (hx : r x ≤ 0) :
      ‖(fullPhysicalProjection d x).2‖ ≤ 28 := by
    have ht := hTann _ (hTmem x hz)
    have hraw := (hRnonpos _ (hTmem x hz) _).mp hx
    have hh := OAI.Analysis.Calculus.Current.physical_fiber_collar_norm_bound a (fullPhysicalProjection d x).1
      (fullPhysicalProjection d x).2 ha ht.1.le (hraw.trans (by norm_num))
    linarith
  have hboundary' (x : OAI.Analysis.PDE.Dirichlet.CoordinateSpace (d + 2) 3)
      (hxT : (fullPhysicalProjection d x).1 ∈ T) (hx : r x = 0) :
      ∀ᶠ y in 𝓝 x, r y = 0 → u y = 0 ∧
        ‖star (OAI.Analysis.PDE.Dirichlet.quaternionGradient e r y) ᵥ* A y‖ ≤ ε ∧ ‖OAI.Analysis.PDE.Dirichlet.quaternionGradient e u y‖ ≤ G :=
    physical_extension_local_boundary_data a R hReq hRnonpos hTann e A u ε G hboundary hxT hx
  have hreg (x : OAI.Analysis.PDE.Dirichlet.CoordinateSpace (d + 2) 3) (hx : r x = 0) :
      fderiv ℝ r x ≠ 0 ∨ (fun y => η (timeProjection (d + 1) 3 y)) =ᶠ[𝓝 x] (fun _ => 0) :=
    fullPhysical_extension_regular_or_test_zero (hR.of_le (by norm_num)) (Subset.refl T) hRreg x hx
  have hcommon' (x : OAI.Analysis.PDE.Dirichlet.CoordinateSpace (d + 2) 3) (hx : r x = 0) :
      ((∀ᶠ y in 𝓝 x, r y = 0 → u y = 0) ∧
        ∃ w : Fin (d + 2) → Quaternion ℝ, w ≠ 0 ∧ OAI.Analysis.PDE.Dirichlet.quaternionHessian e r x *ᵥ w = 0 ∧
          OAI.Analysis.PDE.Dirichlet.quaternionHessian e B x *ᵥ w = 0 ∧ star (OAI.Analysis.PDE.Dirichlet.quaternionGradient e r x) ⬝ᵥ w = 0) ∨
      (fun y => η (timeProjection (d + 1) 3 y)) =ᶠ[𝓝 x] (fun _ => 0) := by
    by_cases hxT : (fullPhysicalProjection d x).1 ∈ T
    · refine Or.inl ⟨(hboundary' x hxT hx).mono (fun y hy hy0 => (hy hy0).1), ?_⟩
      apply physical_extension_common_kernel a R hReq hRnonpos e B hxT hx
      exact hcommon x (hTann _ hxT)
        ((physical_extension_boundary_germ a R hReq hRnonpos hxT hx).eq_of_nhds.symm.trans hx)
    · exact Or.inr (time_test_eventually_zero_of_notMem (Subset.refl T) hxT)
  have hdiv' (x : OAI.Analysis.PDE.Dirichlet.CoordinateSpace (d + 2) 3) (hx : x ∈ S) :
      (∀ j, OAI.Analysis.Calculus.Quaternion.strongDivergence e (fun p => fderiv ℝ A x (OAI.Analysis.PDE.Dirichlet.coordinateVector p)) j = 0) ∨
      (fun y => η (timeProjection (d + 1) 3 y)) =ᶠ[𝓝 x] (fun _ => 0) := by
    by_cases hz : timeProjection (d + 1) 3 x ∈ tsupport η
    · exact Or.inl (hdiv x (hactive x hx hz))
    · exact Or.inr (time_test_zero_off_tsupport hz)
  have hW : ∀ j : ℕ, (∫ x in euclideanCoordinates c ⁻¹' Icc lo hi,
      normalCutoffWeight (r x) j * ‖η (timeProjection (d + 1) 3 x)‖) ≤
      physicalCutoffConstant b * ∫ z, ‖η z‖ :=
    (Classical.choose_spec (exists_uniform_physical_weighted_cutoff_bound b)).2
      a ha T (fun τ hτ => ⟨(hTann τ hτ).1.le, (hTann τ hτ).2.le⟩)
      R hR.continuous hReq hRneg _ hbox (isBounded_euclidean_cell c lo hi)
      (physicalTimeBox_fiber_subset c b L) η hη.continuous
      (hη.continuous.integrable_of_hasCompactSupport hηs) (Subset.refl T)
  have hfaceA : CompatibleCellFaces c lo hi r (secondGreenFlux OAI.Analysis.PDE.Dirichlet.coordinateVector
      (fun p q x => OAI.Analysis.Calculus.Quaternion.realCoefficients e (A x) p q) u (fun x => η (timeProjection (d + 1) 3 x))) := by
    apply physical_time_box_secondGreen_faces c L R η hLs hbound _ u _ hup
    intro p q j x
    rw [hAp j x]
  have hfaceC := physical_time_box_cofactor_faces c L R η hLs hbound e B u hBp hup
  have hweak := combined_fiber_energy_localized_weak_bound e he c lo hi
    (physicalTimeBoxLower_le_upper c hL.le) hA hAh hdiv' hr hB hu hη hηpos
    (fun x _ hx => hreg x hx) hcommon' hlam
    (fun x hx hz => hApos x (hactive x hx (subset_tsupport η hz)))
    (fun x hx hz => hDpos x (hactive x hx (subset_tsupport η hz)))
    (fun x hx hz => hequation x (hactive x hx (subset_tsupport η hz)))
    (fun x hx hz => hann x (hactive x hx (subset_tsupport η hz)))
    (fun x hx hz => hBdet x (hactive x hx (subset_tsupport η hz)))
    (fun x hx hz t ht => spatial_hessian_segment_posSemidef e
      (hB.of_le (by norm_num)) (hu.of_le (by norm_num)) x
      (hBpos x (hactive x hx (laplacian_nonzero_mem_tsupport hz)))
      (hDpos x (hactive x hx (laplacian_nonzero_mem_tsupport hz))).posSemidef ht)
    hε hG hW
    (fun x _ hx => by
      by_cases hxT : (fullPhysicalProjection d x).1 ∈ T
      · exact Or.inl ⟨fullPhysical_extension_regular (hR.of_le (by norm_num))
          (hRreg _ hxT _ hx), hboundary' x hxT hx⟩
      · exact Or.inr (time_test_eventually_zero_of_notMem (Subset.refl T) hxT))
    hfaceA hfaceC
  have heq := physicalTimeBox_weak_energy_eq c b L a ha η
    (fun z hz => ⟨(hηann z hz).1.le, (hηann z hz).2.le⟩)
    (fun z hz j => ⟨(hLs z hz j).1.le, (hLs z hz j).2.le⟩) R
    (fun z hz q => hRneg _ (mem_image_of_mem energyComplexTime hz) q) e lam A B u
  change (∫ z, Laplacian.laplacian η z * setFiberCombinedEnergy e lam
    ((euclideanCoordinates c ⁻¹' Icc lo hi) ∩ {x | r x < 0}) A B u z) ≤
      (d + 2 : ℕ) * ε * G * (physicalCutoffConstant b * ∫ z, ‖η z‖) at hweak
  rw [heq] at hweak
  simpa only [Real.norm_eq_abs, abs_of_nonneg (hηpos _), mul_assoc] using hweak

end OAI.Analysis.PDE.Green

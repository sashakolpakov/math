import OAI.Analysis.PDE.Green.CombinedDensity
import OAI.Analysis.PDE.Green.CurrentTime
import OAI.Analysis.PDE.Green.FiberCutoff

/-! Distributional propagation of the actual combined moving-fiber energy. -/

noncomputable section
namespace OAI.Analysis.PDE.Green

open Set Matrix _root_.MeasureTheory OAI.Analysis.Calculus.Quaternion OAI.Analysis.PDE.Dirichlet OAI.LinearAlgebra.Moore
open scoped Matrix.Norms.Elementwise MatrixOrder ComplexOrder

theorem reverse_sub_le_of_norm_sub_le {x y c : ℝ} (h : ‖x - y‖ ≤ c) : y - x ≤ c := by
  have hh := neg_le_abs (x - y)
  rw [← Real.norm_eq_abs] at hh
  linarith

/-- The source's weak propagation inequality, derived from the determinant
equation, the actual current divergence, and quantitative lateral flux. -/
theorem combined_fiber_energy_weak_bound {n s m : ℕ} (e : Fin s → Quaternion ℝ)
    (he : ∀ α β, (e α * star (e β)).re = if α = β then 1 else 0)
    (c : (Fin (n + 1) × Fin s) ≃ Fin (m + 1)) (a b : Fin (m + 1) → ℝ) (hab : a ≤ b)
    {A : OAI.Analysis.PDE.Dirichlet.CoordinateSpace (n + 1) s → Matrix (Fin (n + 1)) (Fin (n + 1)) (Quaternion ℝ)}
    (hA : ContDiff ℝ 1 A) (hAh : ∀ x, (A x).IsHermitian)
    (hdiv : ∀ x j, OAI.Analysis.Calculus.Quaternion.strongDivergence e (fun p => fderiv ℝ A x (OAI.Analysis.PDE.Dirichlet.coordinateVector p)) j = 0)
    {r B u : OAI.Analysis.PDE.Dirichlet.CoordinateSpace (n + 1) s → ℝ} {η : OAI.Analysis.PDE.Dirichlet.CoordinateSpace 1 s → ℝ}
    (hr : ContDiff ℝ 2 r) (hB : ContDiff ℝ 3 B) (hu : ContDiff ℝ 3 u)
    (hη : ContDiff ℝ 3 η) (hηi : Integrable η) (hηpos : ∀ z, 0 ≤ η z)
    (hrne : ∀ x ∈ euclideanCoordinates c ⁻¹' Icc a b, r x = 0 → fderiv ℝ r x ≠ 0)
    (huz : ∀ x, r x = 0 → u x = 0)
    (hcommon : ∀ x, r x = 0 → ∃ w : Fin (n + 1) → Quaternion ℝ, w ≠ 0 ∧
      OAI.Analysis.PDE.Dirichlet.quaternionHessian e r x *ᵥ w = 0 ∧ OAI.Analysis.PDE.Dirichlet.quaternionHessian e B x *ᵥ w = 0 ∧
      star (OAI.Analysis.PDE.Dirichlet.quaternionGradient e r x) ⬝ᵥ w = 0)
    {lam : ℝ} (hlam : 0 < lam)
    (hApos : ∀ x ∈ (euclideanCoordinates c ⁻¹' Icc a b) ∩ {x | r x < 0},
      (OAI.LinearAlgebra.Moore.complexify (A x)).PosSemidef)
    (hBpos : ∀ x ∈ (euclideanCoordinates c ⁻¹' Icc a b) ∩ {x | r x < 0},
      (OAI.LinearAlgebra.Moore.complexify ((OAI.Analysis.PDE.Dirichlet.quaternionHessian e B x).submatrix Fin.succ Fin.succ)).PosSemidef)
    (hDpos : ∀ x ∈ (euclideanCoordinates c ⁻¹' Icc a b) ∩ {x | r x < 0},
      (OAI.LinearAlgebra.Moore.complexify ((OAI.Analysis.PDE.Dirichlet.quaternionHessian e (fun y => B y + u y) x).submatrix
        Fin.succ Fin.succ)).PosDef)
    (hequation : ∀ x ∈ (euclideanCoordinates c ⁻¹' Icc a b) ∩ {x | r x < 0},
      OAI.LinearAlgebra.Moore.mooreDet n ((OAI.Analysis.PDE.Dirichlet.quaternionHessian e (fun y => B y + u y) x).submatrix
        Fin.succ Fin.succ) = lam * (A x 0 0).re)
    (hann : ∀ x ∈ (euclideanCoordinates c ⁻¹' Icc a b) ∩ {x | r x < 0},
      OAI.LinearAlgebra.Moore.realTrace (A x * OAI.Analysis.PDE.Dirichlet.quaternionHessian e B x) = 0)
    (hBdet : ∀ x ∈ (euclideanCoordinates c ⁻¹' Icc a b) ∩ {x | r x < 0},
      OAI.LinearAlgebra.Moore.mooreDet (n + 1) (OAI.Analysis.PDE.Dirichlet.quaternionHessian e B x) = 0)
    {ε G M : ℝ} (hε : 0 ≤ ε) (hG : 0 ≤ G)
    (hM : ∀ z k, (∫ y in (fiberEmbedding n s z) ⁻¹' (euclideanCoordinates c ⁻¹' Icc a b),
      normalCutoffWeight (r (fiberEmbedding n s z y)) k) ≤ M)
    (hrow : ∀ x, r x = 0 → ‖star (OAI.Analysis.PDE.Dirichlet.quaternionGradient e r x) ᵥ* A x‖ ≤ ε)
    (hgrad : ∀ x, r x = 0 → ‖OAI.Analysis.PDE.Dirichlet.quaternionGradient e u x‖ ≤ G)
    (hfaceA : CompatibleCellFaces c a b r (secondGreenFlux OAI.Analysis.PDE.Dirichlet.coordinateVector
      (fun p q x => OAI.Analysis.Calculus.Quaternion.realCoefficients e (A x) p q) u (fun x => η (timeProjection n s x))))
    (hfaceC : ∀ t : ℝ, CompatibleCellFaces c a b r (secondGreenFlux OAI.Analysis.PDE.Dirichlet.coordinateVector
      (fun p q x => OAI.Analysis.Calculus.Quaternion.realCoefficients e (OAI.LinearAlgebra.Moore.mooreCofactor (n + 1)
        (OAI.Analysis.PDE.Dirichlet.quaternionHessian e (fun y => B y + t * u y) x)) p q) u
      (fun x => η (timeProjection n s x)))) :
    (∫ z, Laplacian.laplacian η z * setFiberCombinedEnergy e lam
      ((euclideanCoordinates c ⁻¹' Icc a b) ∩ {x | r x < 0}) A B u z) ≤
        (n + 1 : ℕ) * ε * G * M * ∫ z, ‖η z‖ := by
  let S := (euclideanCoordinates c ⁻¹' Icc a b) ∩ {x | r x < 0}
  let P := spatialPencilEnergyDensity e B u
  let D := fun x => OAI.LinearAlgebra.Moore.mooreDet (n + 1) (OAI.Analysis.PDE.Dirichlet.quaternionHessian e (fun y => B y + u y) x)
  let J := fun x => OAI.LinearAlgebra.Moore.realTrace (A x * OAI.Analysis.PDE.Dirichlet.quaternionHessian e u x)
  let U := fun x => u x * (A x 0 0).re
  have hbox : MeasurableSet (euclideanCoordinates c ⁻¹' Icc a b) :=
    (isClosed_Icc.preimage (euclideanCoordinates c).continuous).measurableSet
  have hS : MeasurableSet S := hbox.inter (isOpen_lt hr.continuous continuous_const).measurableSet
  have hb : Bornology.IsBounded S := (isBounded_euclidean_cell c a b).subset inter_subset_left
  have hu2 : ContDiff ℝ 2 u := hu.of_le (by norm_num)
  have hB2 : ContDiff ℝ 2 B := hB.of_le (by norm_num)
  have hP : Continuous P := continuous_spatialPencilEnergyDensity e hB hu
  have hD : Continuous D := by
    simpa only [D] using! (OAI.LinearAlgebra.Moore.continuous_mooreDet (n + 1)).comp
      (OAI.Analysis.PDE.Energy.continuous_quaternionHessian_three e (hB.add hu))
  have hJ : Continuous J := continuous_current_pairing e hA.continuous hu
  have hU : Continuous U := hu.continuous.mul (continuous_current_mass hA.continuous)
  have hΔ : Continuous (fun x => Laplacian.laplacian η (timeProjection n s x)) :=
    (continuous_time_laplacian e he hη).comp (timeProjection n s).continuous
  have hηc : Continuous (fun x => η (timeProjection n s x)) :=
    hη.continuous.comp (timeProjection n s).continuous
  have hIP : IntegrableOn (fun x => Laplacian.laplacian η (timeProjection n s x) * P x) S :=
    OAI.Analysis.PDE.Energy.continuous_integrableOn_bounded hb (hΔ.mul hP)
  have hIU : IntegrableOn (fun x => Laplacian.laplacian η (timeProjection n s x) * U x) S :=
    OAI.Analysis.PDE.Energy.continuous_integrableOn_bounded hb (hΔ.mul hU)
  have hID : IntegrableOn (fun x => η (timeProjection n s x) * D x) S :=
    OAI.Analysis.PDE.Energy.continuous_integrableOn_bounded hb (hηc.mul hD)
  have hIJ : IntegrableOn (fun x => η (timeProjection n s x) * J x) S :=
    OAI.Analysis.PDE.Energy.continuous_integrableOn_bounded hb (hηc.mul hJ)
  have hW (k : ℕ) : (∫ x in euclideanCoordinates c ⁻¹' Icc a b,
      normalCutoffWeight (r x) k * ‖η (timeProjection n s x)‖) ≤ M * ∫ z, ‖η z‖ :=
    weighted_normalCutoff_bound_of_fibers hbox (isBounded_euclidean_cell c a b)
      hr.continuous hη.continuous hηi hM k
  have hgreen := current_time_test_bound e he c a b hab hA hAh hdiv hu2
    (hη.of_le (by norm_num)) hr hrne huz hε hG hW hrow hgrad hfaceA
  change ‖(∫ x in S, Laplacian.laplacian η (timeProjection n s x) * U x) -
    ∫ x in S, η (timeProjection n s x) * J x‖ ≤
      (n + 1 : ℕ) * ε * G * (M * ∫ z, ‖η z‖) at hgreen
  have henergy : (∫ x in S, Laplacian.laplacian η (timeProjection n s x) * P x) =
      ∫ x in S, η (timeProjection n s x) * D x := by
    have hh := determinant_energy_weak_time_laplacian_cell e he c a b hab hr hu hB hη
      hrne huz hcommon (fun x hx t ht => spatial_hessian_segment_posSemidef e hB2 hu2 x
        (hBpos x hx) (hDpos x hx).posSemidef ht) hfaceC
    apply hh.trans
    apply setIntegral_congr_fun hS
    intro x hx
    dsimp only [D]
    rw [hBdet x hx, sub_zero]
  have hinterior : lam⁻¹ * (∫ x in S, η (timeProjection n s x) * D x) ≤
      ∫ x in S, η (timeProjection n s x) * J x := by
    rw [← integral_const_mul]
    apply setIntegral_mono_on (hID.const_mul _) hIJ hS
    intro x hx
    have hh := OAI.Analysis.PDE.Energy.current_hessian_energy_inequality e hB2 hu2 (A x) (hApos x hx) x
      (hDpos x hx) hlam (hequation x hx) (hann x hx)
    change lam⁻¹ * (η (timeProjection n s x) * D x) ≤ η (timeProjection n s x) * J x
    calc
      _ = η (timeProjection n s x) * (lam⁻¹ * D x) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hh (hηpos _)
  have hsplit : (∫ x in S, Laplacian.laplacian η (timeProjection n s x) *
      combinedEnergyDensity e lam A B u x) =
      -(∫ x in S, Laplacian.laplacian η (timeProjection n s x) * U x) +
        lam⁻¹ * (∫ x in S, Laplacian.laplacian η (timeProjection n s x) * P x) := by
    calc
      _ = ∫ x in S, -(Laplacian.laplacian η (timeProjection n s x) * U x) +
          lam⁻¹ * (Laplacian.laplacian η (timeProjection n s x) * P x) := by
        apply integral_congr_ae
        filter_upwards [] with x
        dsimp only [combinedEnergyDensity, U, P]
        ring
      _ = _ := by
        have hiu : IntegrableOn (fun x => -(Laplacian.laplacian η (timeProjection n s x) * U x)) S :=
          hIU.neg
        have hip : IntegrableOn (fun x => lam⁻¹ * (Laplacian.laplacian η (timeProjection n s x) * P x)) S :=
          hIP.const_mul lam⁻¹
        rw [integral_add hiu hip, integral_neg, integral_const_mul]
  have hfull : (∫ x in S, Laplacian.laplacian η (timeProjection n s x) *
      combinedEnergyDensity e lam A B u x) ≤ (n + 1 : ℕ) * ε * G * (M * ∫ z, ‖η z‖) := by
    rw [hsplit, henergy]
    have hnorm : (∫ x in S, η (timeProjection n s x) * J x) -
        (∫ x in S, Laplacian.laplacian η (timeProjection n s x) * U x) ≤
          (n + 1 : ℕ) * ε * G * (M * ∫ z, ‖η z‖) :=
      reverse_sub_le_of_norm_sub_le hgreen
    linarith
  have hIF : IntegrableOn (fun x => Laplacian.laplacian η (timeProjection n s x) *
      combinedEnergyDensity e lam A B u x) S :=
    OAI.Analysis.PDE.Energy.continuous_integrableOn_bounded hb
      (hΔ.mul (continuous_combinedEnergyDensity e lam hA.continuous hB hu))
  change (∫ z, Laplacian.laplacian η z * ∫ y in (fiberEmbedding n s z) ⁻¹' S,
    combinedEnergyDensity e lam A B u (fiberEmbedding n s z y)) ≤ _
  rw [← integral_set_time_weight hS _ hIF]
  simpa only [mul_assoc] using hfull

end OAI.Analysis.PDE.Green

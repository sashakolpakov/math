import OAI.Analysis.PDE.Green.CellPencil
import OAI.Analysis.PDE.Green.FiberIntegral

/-! Moving fibers of periodic cells and the determinant-energy identity. -/

noncomputable section
namespace OAI.Analysis.PDE.Green

open Set Matrix _root_.MeasureTheory OAI.Analysis.Calculus.Quaternion OAI.Analysis.PDE.Dirichlet OAI.LinearAlgebra.Moore
open scoped MatrixOrder ComplexOrder

theorem integral_set_fibers {n s : ℕ} {S : Set (OAI.Analysis.PDE.Dirichlet.CoordinateSpace (n + 1) s)}
    (hS : MeasurableSet S) {f : OAI.Analysis.PDE.Dirichlet.CoordinateSpace (n + 1) s → ℝ}
    (hf : IntegrableOn f S) :
    (∫ x in S, f x) = ∫ z : OAI.Analysis.PDE.Dirichlet.CoordinateSpace 1 s,
      ∫ y in (fiberEmbedding n s z) ⁻¹' S, f (fiberEmbedding n s z y) := by
  rw [← integral_indicator hS,
    integral_fiberEmbedding ((integrable_indicator_iff hS).2 hf)]
  apply integral_congr_ae
  filter_upwards [] with z
  have hz : Continuous (fun y => fiberEmbedding n s z y) :=
    (continuous_fiberEmbedding n s).comp (continuous_const.prodMk continuous_id)
  rw [← integral_indicator (hS.preimage hz.measurable)]
  apply integral_congr_ae
  filter_upwards [] with y
  rfl

theorem integral_set_time_weight {n s : ℕ} {S : Set (OAI.Analysis.PDE.Dirichlet.CoordinateSpace (n + 1) s)}
    (hS : MeasurableSet S) {f : OAI.Analysis.PDE.Dirichlet.CoordinateSpace (n + 1) s → ℝ}
    (ρ : OAI.Analysis.PDE.Dirichlet.CoordinateSpace 1 s → ℝ)
    (hf : IntegrableOn (fun x => ρ (timeProjection n s x) * f x) S) :
    (∫ x in S, ρ (timeProjection n s x) * f x) =
      ∫ z : OAI.Analysis.PDE.Dirichlet.CoordinateSpace 1 s, ρ z *
        ∫ y in (fiberEmbedding n s z) ⁻¹' S, f (fiberEmbedding n s z y) := by
  rw [integral_set_fibers hS hf]
  apply integral_congr_ae
  filter_upwards [] with z
  simp only [timeProjection_fiberEmbedding]
  rw [integral_const_mul]

def setFiberDeterminantEnergy {n s : ℕ} (e : Fin s → Quaternion ℝ)
    (S : Set (OAI.Analysis.PDE.Dirichlet.CoordinateSpace (n + 1) s))
    (B u : OAI.Analysis.PDE.Dirichlet.CoordinateSpace (n + 1) s → ℝ) (z : OAI.Analysis.PDE.Dirichlet.CoordinateSpace 1 s) : ℝ :=
  ∫ y in (fiberEmbedding n s z) ⁻¹' S,
    spatialPencilEnergyDensity e B u (fiberEmbedding n s z y)

def setFiberDeterminantDifference {n s : ℕ} (e : Fin s → Quaternion ℝ)
    (S : Set (OAI.Analysis.PDE.Dirichlet.CoordinateSpace (n + 1) s))
    (B u : OAI.Analysis.PDE.Dirichlet.CoordinateSpace (n + 1) s → ℝ) (z : OAI.Analysis.PDE.Dirichlet.CoordinateSpace 1 s) : ℝ :=
  ∫ y in (fiberEmbedding n s z) ⁻¹' S,
    OAI.LinearAlgebra.Moore.mooreDet (n + 1) (OAI.Analysis.PDE.Dirichlet.quaternionHessian e (fun x => B x + u x) (fiberEmbedding n s z y)) -
      OAI.LinearAlgebra.Moore.mooreDet (n + 1) (OAI.Analysis.PDE.Dirichlet.quaternionHessian e B (fiberEmbedding n s z y))

/-- The actual moving-fiber energy on a periodic cell has the claimed weak
time Laplacian. No boundedness of the full periodic domain is required. -/
theorem cellFiberDeterminantEnergy_weak_laplacian {n s m : ℕ}
    (e : Fin s → Quaternion ℝ)
    (he : ∀ α β, (e α * star (e β)).re = if α = β then 1 else 0)
    (c : (Fin (n + 1) × Fin s) ≃ Fin (m + 1))
    (a b : Fin (m + 1) → ℝ) (hab : a ≤ b)
    {r u B : OAI.Analysis.PDE.Dirichlet.CoordinateSpace (n + 1) s → ℝ} {η : OAI.Analysis.PDE.Dirichlet.CoordinateSpace 1 s → ℝ}
    (hr : ContDiff ℝ 2 r) (hu : ContDiff ℝ 3 u) (hB : ContDiff ℝ 3 B)
    (hη : ContDiff ℝ 3 η)
    (hrne : ∀ x ∈ euclideanCoordinates c ⁻¹' Icc a b, r x = 0 → fderiv ℝ r x ≠ 0)
    (huz : ∀ y, r y = 0 → u y = 0)
    (hcommon : ∀ x, r x = 0 → ∃ w : Fin (n + 1) → Quaternion ℝ, w ≠ 0 ∧
      OAI.Analysis.PDE.Dirichlet.quaternionHessian e r x *ᵥ w = 0 ∧ OAI.Analysis.PDE.Dirichlet.quaternionHessian e B x *ᵥ w = 0 ∧
      star (OAI.Analysis.PDE.Dirichlet.quaternionGradient e r x) ⬝ᵥ w = 0)
    (hspatial : ∀ x ∈ (euclideanCoordinates c ⁻¹' Icc a b) ∩ {x | r x < 0},
      ∀ t ∈ Icc (0 : ℝ) 1,
      (OAI.LinearAlgebra.Moore.complexify ((OAI.Analysis.PDE.Dirichlet.quaternionHessian e (fun y => B y + t * u y) x).submatrix
        Fin.succ Fin.succ)).PosSemidef)
    (hface : ∀ t : ℝ, CompatibleCellFaces c a b r (secondGreenFlux OAI.Analysis.PDE.Dirichlet.coordinateVector
      (fun p q x => OAI.Analysis.Calculus.Quaternion.realCoefficients e (OAI.LinearAlgebra.Moore.mooreCofactor (n + 1)
        (OAI.Analysis.PDE.Dirichlet.quaternionHessian e (fun y => B y + t * u y) x)) p q) u
      (fun x => η (timeProjection n s x)))) :
    (∫ z, Laplacian.laplacian η z * setFiberDeterminantEnergy e
      ((euclideanCoordinates c ⁻¹' Icc a b) ∩ {x | r x < 0}) B u z) =
    ∫ z, η z * setFiberDeterminantDifference e
      ((euclideanCoordinates c ⁻¹' Icc a b) ∩ {x | r x < 0}) B u z := by
  have hb := (isBounded_euclidean_cell c a b).subset
    (inter_subset_left : ((euclideanCoordinates c ⁻¹' Icc a b) ∩ {x | r x < 0}) ⊆ _)
  have hS : MeasurableSet ((euclideanCoordinates c ⁻¹' Icc a b) ∩ {x | r x < 0}) :=
    (isClosed_Icc.preimage (euclideanCoordinates c).continuous).measurableSet.inter
      (isOpen_lt hr.continuous continuous_const).measurableSet
  have hden := continuous_spatialPencilEnergyDensity e hB hu
  have hΔ := continuous_time_laplacian e he hη
  have hd1 : Continuous (fun x => OAI.LinearAlgebra.Moore.mooreDet (n + 1)
      (OAI.Analysis.PDE.Dirichlet.quaternionHessian e (fun y => B y + u y) x)) := by
    simpa only using! (OAI.LinearAlgebra.Moore.continuous_mooreDet (n + 1)).comp
      (OAI.Analysis.PDE.Energy.continuous_quaternionHessian_three e (hB.add hu))
  have hd0 : Continuous (fun x => OAI.LinearAlgebra.Moore.mooreDet (n + 1) (OAI.Analysis.PDE.Dirichlet.quaternionHessian e B x)) := by
    simpa only using! (OAI.LinearAlgebra.Moore.continuous_mooreDet (n + 1)).comp
      (OAI.Analysis.PDE.Energy.continuous_quaternionHessian_three e hB)
  have hi1 := OAI.Analysis.PDE.Energy.continuous_integrableOn_bounded hb
    ((hΔ.comp (timeProjection n s).continuous).mul hden)
  have hi2 : IntegrableOn (fun x => η (timeProjection n s x) *
      (OAI.LinearAlgebra.Moore.mooreDet (n + 1) (OAI.Analysis.PDE.Dirichlet.quaternionHessian e (fun y => B y + u y) x) -
        OAI.LinearAlgebra.Moore.mooreDet (n + 1) (OAI.Analysis.PDE.Dirichlet.quaternionHessian e B x)))
      ((euclideanCoordinates c ⁻¹' Icc a b) ∩ {x | r x < 0}) :=
    OAI.Analysis.PDE.Energy.continuous_integrableOn_bounded hb
      ((hη.continuous.comp (timeProjection n s).continuous).mul (hd1.sub hd0))
  unfold setFiberDeterminantEnergy setFiberDeterminantDifference
  rw [← integral_set_time_weight hS _ hi1, ← integral_set_time_weight hS _ hi2]
  exact determinant_energy_weak_time_laplacian_cell e he c a b hab hr hu hB hη
    hrne huz hcommon hspatial hface

end OAI.Analysis.PDE.Green

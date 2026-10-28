import OAI.Analysis.PDE.Green.PencilIntegral

/-! Translation periodicity of derivatives and quaternionic Green fluxes. -/

noncomputable section
namespace OAI.Analysis.PDE.Green

open Set Matrix _root_.MeasureTheory OAI.Analysis.Calculus.Quaternion OAI.Analysis.PDE.Dirichlet OAI.LinearAlgebra.Moore

theorem fderiv_periodic_add
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (f : E → F) (w : E) (h : ∀ x, f (x + w) = f x) (x : E) :
    fderiv ℝ f (x + w) = fderiv ℝ f x := by
  rw [← fderiv_comp_add_right w]
  congr 1
  exact funext h

theorem second_fderiv_periodic_add
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (f : E → F) (w : E) (h : ∀ x, f (x + w) = f x) (x : E) :
    fderiv ℝ (fderiv ℝ f) (x + w) = fderiv ℝ (fderiv ℝ f) x :=
  fderiv_periodic_add (fderiv ℝ f) w (fderiv_periodic_add f w h) x

theorem quaternionHessian_periodic_add {n s : ℕ} (e : Fin s → Quaternion ℝ)
    (f : OAI.Analysis.PDE.Dirichlet.CoordinateSpace n s → ℝ) (w : OAI.Analysis.PDE.Dirichlet.CoordinateSpace n s)
    (h : ∀ x, f (x + w) = f x) (x : OAI.Analysis.PDE.Dirichlet.CoordinateSpace n s) :
    OAI.Analysis.PDE.Dirichlet.quaternionHessian e f (x + w) = OAI.Analysis.PDE.Dirichlet.quaternionHessian e f x := by
  unfold OAI.Analysis.PDE.Dirichlet.quaternionHessian OAI.Analysis.PDE.Dirichlet.realHessian
  rw [second_fderiv_periodic_add f w h]

theorem secondGreenFlux_periodic_add
    {E I : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [Fintype I]
    (d : I → E) (K : I → I → E → ℝ) (u v : E → ℝ) (w : E)
    (hK : ∀ i j x, K i j (x + w) = K i j x)
    (hu : ∀ x, u (x + w) = u x) (hv : ∀ x, v (x + w) = v x)
    (i : I) (x : E) :
    secondGreenFlux d K u v i (x + w) = secondGreenFlux d K u v i x := by
  simp only [secondGreenFlux, realFlux, hu, hv, hK,
    fderiv_periodic_add u w hu, fderiv_periodic_add v w hv]

theorem secondGreenFlux_zero_of_test_jet
    {E I : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [Fintype I]
    (d : I → E) (K : I → I → E → ℝ) (u v : E → ℝ) (x : E)
    (hv : v x = 0) (hdv : fderiv ℝ v x = 0) (i : I) :
    secondGreenFlux d K u v i x = 0 := by
  simp [secondGreenFlux, realFlux, hv, hdv]

theorem cofactor_secondGreenFlux_periodic_add {n s : ℕ} (e : Fin s → Quaternion ℝ)
    (ψ u v : OAI.Analysis.PDE.Dirichlet.CoordinateSpace n s → ℝ) (w : OAI.Analysis.PDE.Dirichlet.CoordinateSpace n s)
    (hψ : ∀ x, ψ (x + w) = ψ x)
    (hu : ∀ x, u (x + w) = u x) (hv : ∀ x, v (x + w) = v x)
    (i : Fin n × Fin s) (x : OAI.Analysis.PDE.Dirichlet.CoordinateSpace n s) :
    secondGreenFlux OAI.Analysis.PDE.Dirichlet.coordinateVector
      (fun p q y => OAI.Analysis.Calculus.Quaternion.realCoefficients e (OAI.LinearAlgebra.Moore.mooreCofactor n (OAI.Analysis.PDE.Dirichlet.quaternionHessian e ψ y)) p q)
      u v i (x + w) =
    secondGreenFlux OAI.Analysis.PDE.Dirichlet.coordinateVector
      (fun p q y => OAI.Analysis.Calculus.Quaternion.realCoefficients e (OAI.LinearAlgebra.Moore.mooreCofactor n (OAI.Analysis.PDE.Dirichlet.quaternionHessian e ψ y)) p q)
      u v i x := by
  apply secondGreenFlux_periodic_add _ _ _ _ w _ hu hv
  intro p q y
  rw [quaternionHessian_periodic_add e ψ w hψ]

theorem insertNth_eq_add_single {m : ℕ} (i : Fin (m + 1)) (a b : ℝ) (y : Fin m → ℝ) :
    i.insertNth b y = i.insertNth a y + (Pi.single i (b - a) : Fin (m + 1) → ℝ) := by
  ext j
  rcases eq_or_ne i j with rfl | hij
  · simp
  · obtain ⟨k, rfl⟩ := Fin.exists_succAbove_eq hij.symm
    simp

end OAI.Analysis.PDE.Green

import OAI.Analysis.PDE.Concentration.Lattice.SmallGreen
import OAI.Analysis.PDE.Green.NormalPairing
import OAI.Analysis.PDE.Green.TimeTest

/-! The time-test current identity with only local lateral boundary assumptions. -/

noncomputable section
namespace OAI.Analysis.PDE.Concentration

open Set Filter Matrix _root_.MeasureTheory OAI.Analysis.PDE.Green OAI.Analysis.Calculus.Quaternion OAI.Analysis.PDE.Dirichlet OAI.LinearAlgebra.Moore
open scoped Matrix.Norms.Elementwise Topology

theorem quaternion_current_second_green_lattice_localized_bound {n s m : ℕ} (e : Fin s → Quaternion ℝ)
    (c : (Fin n × Fin s) ≃ Fin (m + 1)) (L : (Fin (m + 1) → ℝ) ≃L[ℝ] (Fin (m + 1) → ℝ))
    (a b : Fin (m + 1) → ℝ) (hab : a ≤ b)
    {A : OAI.Analysis.PDE.Dirichlet.CoordinateSpace n s → Matrix (Fin n) (Fin n) (Quaternion ℝ)}
    (hA : ContDiff ℝ 1 A) (hAh : ∀ x, (A x).IsHermitian)
    {r u v : OAI.Analysis.PDE.Dirichlet.CoordinateSpace n s → ℝ}
    (hdiv : ∀ x ∈ (euclideanLatticeCell c L a b) ∩ {x | r x < 0},
      (∀ j, OAI.Analysis.Calculus.Quaternion.strongDivergence e (fun p => fderiv ℝ A x (OAI.Analysis.PDE.Dirichlet.coordinateVector p)) j = 0) ∨
      v =ᶠ[𝓝 x] (fun _ => 0))
    (hu : ContDiff ℝ 2 u) (hv : ContDiff ℝ 2 v) (hr : ContDiff ℝ 2 r)
    {ε G W : ℝ} (hε : 0 ≤ ε) (hG : 0 ≤ G)
    (hW : ∀ k : ℕ, (∫ x in Icc a b,
      OAI.Analysis.PDE.Green.normalCutoffWeight (r ((OAI.Analysis.PDE.Green.euclideanCoordinates c).symm (L x))) k *
        ‖v ((OAI.Analysis.PDE.Green.euclideanCoordinates c).symm (L x))‖) ≤ W)
    (hboundary : ∀ x ∈ euclideanLatticeCell c L a b, r x = 0 →
      (fderiv ℝ r x ≠ 0 ∧ ∀ᶠ y in 𝓝 x, r y = 0 → u y = 0 ∧
        ‖star (OAI.Analysis.PDE.Dirichlet.quaternionGradient e r y) ᵥ* A y‖ ≤ ε ∧ ‖OAI.Analysis.PDE.Dirichlet.quaternionGradient e u y‖ ≤ G) ∨
      v =ᶠ[𝓝 x] (fun _ => 0))
    (hface : CompatibleLatticeFaces c L a b r (OAI.Analysis.PDE.Green.secondGreenFlux OAI.Analysis.PDE.Dirichlet.coordinateVector
      (fun p q x => OAI.Analysis.Calculus.Quaternion.realCoefficients e (A x) p q) u v)) :
    ‖(∫ x in (euclideanLatticeCell c L a b) ∩ {x | r x < 0},
      u x * OAI.LinearAlgebra.Moore.realTrace (A x * OAI.Analysis.PDE.Dirichlet.quaternionHessian e v x)) -
    ∫ x in (euclideanLatticeCell c L a b) ∩ {x | r x < 0},
      v x * OAI.LinearAlgebra.Moore.realTrace (A x * OAI.Analysis.PDE.Dirichlet.quaternionHessian e u x)‖ ≤ |L.toLinearEquiv.toLinearMap.det| * ((n : ℝ) * ε * G * W) := by
  have hK (p q : Fin n × Fin s) :
      ContDiff ℝ 1 (fun x => OAI.Analysis.Calculus.Quaternion.realCoefficients e (A x) p q) :=
    (OAI.Analysis.PDE.Green.realCoefficientCLM e p q).contDiff.comp hA
  have hKs (p q : Fin n × Fin s) (x : OAI.Analysis.PDE.Dirichlet.CoordinateSpace n s) :
      OAI.Analysis.Calculus.Quaternion.realCoefficients e (A x) p q = OAI.Analysis.Calculus.Quaternion.realCoefficients e (A x) q p :=
    (congrFun (congrFun (OAI.Analysis.Calculus.Quaternion.realCoefficients_isSymm e (A x) (hAh x)) p) q).symm
  have hd : ∀ x ∈ (euclideanLatticeCell c L a b) ∩ {x | r x < 0},
      (∀ q, (∑ p, fderiv ℝ (fun y => OAI.Analysis.Calculus.Quaternion.realCoefficients e (A y) p q) x (OAI.Analysis.PDE.Dirichlet.coordinateVector p)) = 0) ∨
      v =ᶠ[𝓝 x] (fun _ => 0) := by
    intro x hx
    rcases hdiv x hx with h | h
    · apply Or.inl
      intro q
      simp_rw [OAI.Analysis.PDE.Green.fderiv_realCoefficient e _ _ (hA.differentiable (by norm_num) x)]
      exact OAI.Analysis.Calculus.Quaternion.realCoefficients_divergence_zero e _ h q
    · exact Or.inr h
  have hlocal : ∀ x ∈ euclideanLatticeCell c L a b, r x = 0 →
      (fderiv ℝ r x ≠ 0 ∧ ∀ᶠ y in 𝓝 x, r y = 0 → u y = 0 ∧
        ‖OAI.Analysis.PDE.Green.normalRealFlux OAI.Analysis.PDE.Dirichlet.coordinateVector (fun p q y => OAI.Analysis.Calculus.Quaternion.realCoefficients e (A y) p q) r u y‖ ≤
          (n : ℝ) * ε * G) ∨ v =ᶠ[𝓝 x] (fun _ => 0) := by
    intro x hx hrx
    rcases hboundary x hx hrx with ⟨hreg, hlocal⟩ | hz
    · refine Or.inl ⟨hreg, ?_⟩
      filter_upwards [hlocal] with y hy hyr
      exact ⟨(hy hyr).1, OAI.Analysis.PDE.Green.normalRealFlux_bound e A r u y (hy hyr).2.1 (hy hyr).2.2⟩
    · exact Or.inr hz
  have h := real_operator_second_green_lattice_localized_bound c L a b hab
    (fun p q x => OAI.Analysis.Calculus.Quaternion.realCoefficients e (A x) p q) hK hu hv hr hKs hd
    (mul_nonneg (mul_nonneg (Nat.cast_nonneg n) hε) hG) hW hlocal hface
  have hform (f : OAI.Analysis.PDE.Dirichlet.CoordinateSpace n s → ℝ) (hf : ContDiff ℝ 2 f) (x : OAI.Analysis.PDE.Dirichlet.CoordinateSpace n s) :
      OAI.LinearAlgebra.Moore.realTrace (A x * OAI.Analysis.PDE.Dirichlet.quaternionHessian e f x) =
      ∑ p, ∑ q, OAI.Analysis.Calculus.Quaternion.realCoefficients e (A x) p q * OAI.Analysis.PDE.Dirichlet.realHessian f x p q :=
    OAI.Analysis.PDE.Green.realTrace_hessianMap (A x) e (OAI.Analysis.PDE.Dirichlet.realHessian f x) (OAI.Analysis.PDE.Dirichlet.realHessian_isSymm hf.contDiffAt)
  simpa only [hform u hu, hform v hv, OAI.Analysis.PDE.Dirichlet.realHessian, OAI.Analysis.PDE.Dirichlet.coordinateVector] using h

theorem current_time_test_lattice_localized_bound {n s m : ℕ} (e : Fin s → Quaternion ℝ)
    (he : ∀ α β, (e α * star (e β)).re = if α = β then 1 else 0)
    (c : (Fin (n + 1) × Fin s) ≃ Fin (m + 1)) (L : (Fin (m + 1) → ℝ) ≃L[ℝ] (Fin (m + 1) → ℝ))
    (a b : Fin (m + 1) → ℝ) (hab : a ≤ b)
    {A : OAI.Analysis.PDE.Dirichlet.CoordinateSpace (n + 1) s → Matrix (Fin (n + 1)) (Fin (n + 1)) (Quaternion ℝ)}
    (hA : ContDiff ℝ 1 A) (hAh : ∀ x, (A x).IsHermitian)
    {r u : OAI.Analysis.PDE.Dirichlet.CoordinateSpace (n + 1) s → ℝ} {η : OAI.Analysis.PDE.Dirichlet.CoordinateSpace 1 s → ℝ}
    (hdiv : ∀ x ∈ (euclideanLatticeCell c L a b) ∩ {x | r x < 0},
      (∀ j, OAI.Analysis.Calculus.Quaternion.strongDivergence e (fun p => fderiv ℝ A x (OAI.Analysis.PDE.Dirichlet.coordinateVector p)) j = 0) ∨
      (fun y => η (OAI.Analysis.PDE.Green.timeProjection n s y)) =ᶠ[𝓝 x] (fun _ => 0))
    (hu : ContDiff ℝ 2 u) (hη : ContDiff ℝ 2 η) (hr : ContDiff ℝ 2 r)
    {ε G W : ℝ} (hε : 0 ≤ ε) (hG : 0 ≤ G)
    (hW : ∀ k : ℕ, (∫ x in Icc a b,
      OAI.Analysis.PDE.Green.normalCutoffWeight (r ((OAI.Analysis.PDE.Green.euclideanCoordinates c).symm (L x))) k *
        ‖η (OAI.Analysis.PDE.Green.timeProjection n s ((OAI.Analysis.PDE.Green.euclideanCoordinates c).symm (L x)))‖) ≤ W)
    (hboundary : ∀ x ∈ euclideanLatticeCell c L a b, r x = 0 →
      (fderiv ℝ r x ≠ 0 ∧ ∀ᶠ y in 𝓝 x, r y = 0 → u y = 0 ∧
        ‖star (OAI.Analysis.PDE.Dirichlet.quaternionGradient e r y) ᵥ* A y‖ ≤ ε ∧ ‖OAI.Analysis.PDE.Dirichlet.quaternionGradient e u y‖ ≤ G) ∨
      (fun y => η (OAI.Analysis.PDE.Green.timeProjection n s y)) =ᶠ[𝓝 x] (fun _ => 0))
    (hface : CompatibleLatticeFaces c L a b r (OAI.Analysis.PDE.Green.secondGreenFlux OAI.Analysis.PDE.Dirichlet.coordinateVector
      (fun p q x => OAI.Analysis.Calculus.Quaternion.realCoefficients e (A x) p q) u (fun x => η (OAI.Analysis.PDE.Green.timeProjection n s x)))) :
    ‖(∫ x in (euclideanLatticeCell c L a b) ∩ {x | r x < 0},
      Laplacian.laplacian η (OAI.Analysis.PDE.Green.timeProjection n s x) * (u x * (A x 0 0).re)) -
    ∫ x in (euclideanLatticeCell c L a b) ∩ {x | r x < 0},
      η (OAI.Analysis.PDE.Green.timeProjection n s x) * OAI.LinearAlgebra.Moore.realTrace (A x * OAI.Analysis.PDE.Dirichlet.quaternionHessian e u x)‖ ≤
        |L.toLinearEquiv.toLinearMap.det| * ((n + 1 : ℕ) * ε * G * W) := by
  have h := quaternion_current_second_green_lattice_localized_bound e c L a b hab hA hAh hdiv hu
    (hη.comp (OAI.Analysis.PDE.Green.timeProjection n s).contDiff) hr hε hG hW hboundary hface
  have hid (x : OAI.Analysis.PDE.Dirichlet.CoordinateSpace (n + 1) s) :
      u x * OAI.LinearAlgebra.Moore.realTrace (A x * OAI.Analysis.PDE.Dirichlet.quaternionHessian e (fun y => η (OAI.Analysis.PDE.Green.timeProjection n s y)) x) =
        Laplacian.laplacian η (OAI.Analysis.PDE.Green.timeProjection n s x) * (u x * (A x 0 0).re) := by
    rw [OAI.Analysis.PDE.Green.realTrace_mul_time_test e he hη]
    ring
  simpa only [Function.comp_def, hid] using h

end OAI.Analysis.PDE.Concentration

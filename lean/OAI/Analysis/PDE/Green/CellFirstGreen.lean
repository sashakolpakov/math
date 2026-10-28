import OAI.Analysis.PDE.Green.CellQuaternion

/-! First Green identities on periodic cells. The test function vanishes only
on the genuine lateral boundary, not on the artificial periodic faces. -/

noncomputable section
namespace OAI.Analysis.PDE.Green

open Set Matrix _root_.MeasureTheory OAI.Analysis.Calculus.Quaternion OAI.Analysis.PDE.Dirichlet OAI.LinearAlgebra.Moore
open scoped Matrix.Norms.Elementwise

theorem real_operator_first_green_cell
    {ι : Type*} [Fintype ι] [DecidableEq ι] {m : ℕ} (c : ι ≃ Fin (m + 1))
    (a b : Fin (m + 1) → ℝ) (hab : a ≤ b)
    (K : ι → ι → EuclideanSpace ℝ ι → ℝ) {r u v : EuclideanSpace ℝ ι → ℝ}
    (hK : ∀ i j, ContDiff ℝ 1 (K i j))
    (hu : ContDiff ℝ 1 u) (hv : ContDiff ℝ 2 v) (hr : ContDiff ℝ 2 r)
    (hdiv : ∀ x j, ∑ i, fderiv ℝ (K i j) x (EuclideanSpace.single i 1) = 0)
    (hrne : ∀ x ∈ euclideanCoordinates c ⁻¹' Icc a b, r x = 0 → fderiv ℝ r x ≠ 0)
    (huz : ∀ x, r x = 0 → u x = 0)
    (hface : CompatibleCellFaces c a b r
      (fun i x => u x * realFlux (fun j => EuclideanSpace.single j 1) K v i x)) :
    (∫ x in (euclideanCoordinates c ⁻¹' Icc a b) ∩ {x | r x < 0}, u x *
      (∑ i, ∑ j, K i j x * fderiv ℝ (fderiv ℝ v) x
        (EuclideanSpace.single i 1) (EuclideanSpace.single j 1))) =
    -(∫ x in (euclideanCoordinates c ⁻¹' Icc a b) ∩ {x | r x < 0},
      ∑ i, ∑ j, K i j x * fderiv ℝ u x (EuclideanSpace.single i 1) *
        fderiv ℝ v x (EuclideanSpace.single j 1)) := by
  let d : ι → EuclideanSpace ℝ ι := fun i => EuclideanSpace.single i 1
  have hb := (isBounded_euclidean_cell c a b).subset
    (inter_subset_left : ((euclideanCoordinates c ⁻¹' Icc a b) ∩ {x | r x < 0}) ⊆ _)
  have hF := contDiff_realFlux d K hK hv
  have hQ : IntegrableOn (fun x => ∑ i, fderiv ℝ u x (d i) * realFlux d K v i x)
      ((euclideanCoordinates c ⁻¹' Icc a b) ∩ {x | r x < 0}) :=
    OAI.Analysis.PDE.Energy.continuous_integrableOn_bounded hb (continuous_finsetSum _
      (fun i _ => (continuous_directional hu (d i)).mul (hF i).continuous))
  have hO : IntegrableOn (fun x => u x * ∑ i, fderiv ℝ (realFlux d K v i) x (d i))
      ((euclideanCoordinates c ⁻¹' Icc a b) ∩ {x | r x < 0}) :=
    OAI.Analysis.PDE.Energy.continuous_integrableOn_bounded hb (hu.continuous.mul
      (continuous_finsetSum _ (fun i _ => continuous_directional (hF i) (d i))))
  have he := integral_divergence_euclidean_cell_zero c a b hab
    (fun i x => u x * realFlux d K v i x) (fun i => hu.mul (hF i)) hr hrne
    (fun x hx => by simp only [huz x hx, zero_mul, mul_zero, Finset.sum_const_zero]) hface
  change (∫ x in (euclideanCoordinates c ⁻¹' Icc a b) ∩ {x | r x < 0},
    ∑ i, fderiv ℝ (fun y => u y * realFlux d K v i y) x (d i)) = 0 at he
  simp_rw [weightedFlux_divergence d _ hF hu] at he
  rw [integral_add hQ hO] at he
  have hquad (x : EuclideanSpace ℝ ι) :
      (∑ i, fderiv ℝ u x (d i) * realFlux d K v i x) =
        ∑ i, ∑ j, K i j x * fderiv ℝ u x (d i) * fderiv ℝ v x (d j) := by
    simp only [realFlux, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    ring
  simp_rw [hquad, realFlux_divergence d K hK hv hdiv] at he
  exact eq_neg_of_add_eq_zero_right he

theorem quaternion_current_first_green_cell {n s m : ℕ} (e : Fin s → Quaternion ℝ)
    (c : (Fin n × Fin s) ≃ Fin (m + 1)) (a b : Fin (m + 1) → ℝ) (hab : a ≤ b)
    {A : OAI.Analysis.PDE.Dirichlet.CoordinateSpace n s → Matrix (Fin n) (Fin n) (Quaternion ℝ)}
    (hA : ContDiff ℝ 1 A)
    (hdiv : ∀ x j, OAI.Analysis.Calculus.Quaternion.strongDivergence e
      (fun p => fderiv ℝ A x (OAI.Analysis.PDE.Dirichlet.coordinateVector p)) j = 0)
    {r u v : OAI.Analysis.PDE.Dirichlet.CoordinateSpace n s → ℝ}
    (hu : ContDiff ℝ 1 u) (hv : ContDiff ℝ 2 v) (hr : ContDiff ℝ 2 r)
    (hrne : ∀ x ∈ euclideanCoordinates c ⁻¹' Icc a b, r x = 0 → fderiv ℝ r x ≠ 0)
    (huz : ∀ x, r x = 0 → u x = 0)
    (hface : CompatibleCellFaces c a b r (fun p x => u x *
      realFlux OAI.Analysis.PDE.Dirichlet.coordinateVector (fun p q x => OAI.Analysis.Calculus.Quaternion.realCoefficients e (A x) p q) v p x)) :
    (∫ x in (euclideanCoordinates c ⁻¹' Icc a b) ∩ {x | r x < 0},
      u x * OAI.LinearAlgebra.Moore.realTrace (A x * OAI.Analysis.PDE.Dirichlet.quaternionHessian e v x)) =
    -(∫ x in (euclideanCoordinates c ⁻¹' Icc a b) ∩ {x | r x < 0},
      ∑ p, ∑ q, OAI.Analysis.Calculus.Quaternion.realCoefficients e (A x) p q * OAI.Analysis.PDE.Dirichlet.realGradient u x p * OAI.Analysis.PDE.Dirichlet.realGradient v x q) := by
  have hK (p q : Fin n × Fin s) :
      ContDiff ℝ 1 (fun x => OAI.Analysis.Calculus.Quaternion.realCoefficients e (A x) p q) :=
    (realCoefficientCLM e p q).contDiff.comp hA
  have hd (x : OAI.Analysis.PDE.Dirichlet.CoordinateSpace n s) (q : Fin n × Fin s) :
      (∑ p, fderiv ℝ (fun y => OAI.Analysis.Calculus.Quaternion.realCoefficients e (A y) p q) x (OAI.Analysis.PDE.Dirichlet.coordinateVector p)) = 0 := by
    simp_rw [fderiv_realCoefficient e _ _ (hA.differentiable (by norm_num) x)]
    exact OAI.Analysis.Calculus.Quaternion.realCoefficients_divergence_zero e _ (hdiv x) q
  have h := real_operator_first_green_cell c a b hab
    (fun p q x => OAI.Analysis.Calculus.Quaternion.realCoefficients e (A x) p q) hK hu hv hr hd hrne huz hface
  have hform (x : OAI.Analysis.PDE.Dirichlet.CoordinateSpace n s) :
      OAI.LinearAlgebra.Moore.realTrace (A x * OAI.Analysis.PDE.Dirichlet.quaternionHessian e v x) =
      ∑ p, ∑ q, OAI.Analysis.Calculus.Quaternion.realCoefficients e (A x) p q * OAI.Analysis.PDE.Dirichlet.realHessian v x p q :=
    realTrace_hessianMap (A x) e (OAI.Analysis.PDE.Dirichlet.realHessian v x) (OAI.Analysis.PDE.Dirichlet.realHessian_isSymm hv.contDiffAt)
  simpa only [hform, OAI.Analysis.PDE.Dirichlet.realHessian, OAI.Analysis.PDE.Dirichlet.realGradient, OAI.Analysis.PDE.Dirichlet.coordinateVector] using h

end OAI.Analysis.PDE.Green

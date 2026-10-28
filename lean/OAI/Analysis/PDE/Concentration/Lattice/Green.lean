import OAI.Analysis.PDE.Concentration.EuclideanLattice
import OAI.Analysis.PDE.Green.CellFirstGreen

noncomputable section
namespace OAI.Analysis.PDE.Concentration

open Set Matrix _root_.MeasureTheory OAI.Analysis.PDE.Green OAI.Analysis.Calculus.Quaternion OAI.Analysis.PDE.Dirichlet OAI.LinearAlgebra.Moore
open scoped Matrix.Norms.Elementwise

/-- First Green identity for the original real differential operator on a
rotated lattice cell. The chart is used only to cancel artificial faces. -/
theorem real_operator_first_green_lattice
    {ι : Type*} [Fintype ι] [DecidableEq ι] {m : ℕ} (c : ι ≃ Fin (m + 1))
    (L : (Fin (m + 1) → ℝ) ≃L[ℝ] (Fin (m + 1) → ℝ))
    (a b : Fin (m + 1) → ℝ) (hab : a ≤ b)
    (K : ι → ι → EuclideanSpace ℝ ι → ℝ) {r u v : EuclideanSpace ℝ ι → ℝ}
    (hK : ∀ i j, ContDiff ℝ 1 (K i j))
    (hu : ContDiff ℝ 1 u) (hv : ContDiff ℝ 2 v) (hr : ContDiff ℝ 2 r)
    (hdiv : ∀ x j, ∑ i, fderiv ℝ (K i j) x (EuclideanSpace.single i 1) = 0)
    (hrne : ∀ x ∈ euclideanLatticeCell c L a b, r x = 0 → fderiv ℝ r x ≠ 0)
    (huz : ∀ x, r x = 0 → u x = 0)
    (hface : CompatibleLatticeFaces c L a b r
      (fun i x => u x * OAI.Analysis.PDE.Green.realFlux (fun j => EuclideanSpace.single j 1) K v i x)) :
    (∫ x in euclideanLatticeCell c L a b ∩ {x | r x < 0}, u x *
      (∑ i, ∑ j, K i j x * fderiv ℝ (fderiv ℝ v) x
        (EuclideanSpace.single i 1) (EuclideanSpace.single j 1))) =
    -(∫ x in euclideanLatticeCell c L a b ∩ {x | r x < 0},
      ∑ i, ∑ j, K i j x * fderiv ℝ u x (EuclideanSpace.single i 1) *
        fderiv ℝ v x (EuclideanSpace.single j 1)) := by
  let d : ι → EuclideanSpace ℝ ι := fun i => EuclideanSpace.single i 1
  have hb := (isBounded_euclideanLatticeCell c L a b).subset
    (inter_subset_left : (euclideanLatticeCell c L a b ∩ {x | r x < 0}) ⊆ _)
  have hF := OAI.Analysis.PDE.Green.contDiff_realFlux d K hK hv
  have hQ : IntegrableOn (fun x => ∑ i, fderiv ℝ u x (d i) * OAI.Analysis.PDE.Green.realFlux d K v i x)
      (euclideanLatticeCell c L a b ∩ {x | r x < 0}) :=
    OAI.Analysis.PDE.Energy.continuous_integrableOn_bounded hb (continuous_finsetSum _
      (fun i _ => (OAI.Analysis.PDE.Green.continuous_directional hu (d i)).mul (hF i).continuous))
  have hO : IntegrableOn (fun x => u x * ∑ i, fderiv ℝ (OAI.Analysis.PDE.Green.realFlux d K v i) x (d i))
      (euclideanLatticeCell c L a b ∩ {x | r x < 0}) :=
    OAI.Analysis.PDE.Energy.continuous_integrableOn_bounded hb (hu.continuous.mul
      (continuous_finsetSum _ (fun i _ => OAI.Analysis.PDE.Green.continuous_directional (hF i) (d i))))
  have he := integral_divergence_euclidean_lattice_zero c L a b hab
    (fun i x => u x * OAI.Analysis.PDE.Green.realFlux d K v i x) (fun i => hu.mul (hF i)) hr hrne
    (fun x hx => by simp only [huz x hx, zero_mul, mul_zero, Finset.sum_const_zero]) hface
  change (∫ x in euclideanLatticeCell c L a b ∩ {x | r x < 0},
    ∑ i, fderiv ℝ (fun y => u y * OAI.Analysis.PDE.Green.realFlux d K v i y) x (d i)) = 0 at he
  simp_rw [OAI.Analysis.PDE.Green.weightedFlux_divergence d _ hF hu] at he
  rw [integral_add hQ hO] at he
  have hquad (x : EuclideanSpace ℝ ι) :
      (∑ i, fderiv ℝ u x (d i) * OAI.Analysis.PDE.Green.realFlux d K v i x) =
        ∑ i, ∑ j, K i j x * fderiv ℝ u x (d i) * fderiv ℝ v x (d j) := by
    simp only [OAI.Analysis.PDE.Green.realFlux, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    ring
  simp_rw [hquad, OAI.Analysis.PDE.Green.realFlux_divergence d K hK hv hdiv] at he
  exact eq_neg_of_add_eq_zero_right he

theorem quaternion_current_first_green_lattice {n s m : ℕ} (e : Fin s → Quaternion ℝ)
    (c : (Fin n × Fin s) ≃ Fin (m + 1))
    (L : (Fin (m + 1) → ℝ) ≃L[ℝ] (Fin (m + 1) → ℝ))
    (a b : Fin (m + 1) → ℝ) (hab : a ≤ b)
    {A : OAI.Analysis.PDE.Dirichlet.CoordinateSpace n s → Matrix (Fin n) (Fin n) (Quaternion ℝ)}
    (hA : ContDiff ℝ 1 A)
    (hdiv : ∀ x j, OAI.Analysis.Calculus.Quaternion.strongDivergence e
      (fun p => fderiv ℝ A x (OAI.Analysis.PDE.Dirichlet.coordinateVector p)) j = 0)
    {r u v : OAI.Analysis.PDE.Dirichlet.CoordinateSpace n s → ℝ}
    (hu : ContDiff ℝ 1 u) (hv : ContDiff ℝ 2 v) (hr : ContDiff ℝ 2 r)
    (hrne : ∀ x ∈ euclideanLatticeCell c L a b, r x = 0 → fderiv ℝ r x ≠ 0)
    (huz : ∀ x, r x = 0 → u x = 0)
    (hface : CompatibleLatticeFaces c L a b r (fun p x => u x *
      OAI.Analysis.PDE.Green.realFlux OAI.Analysis.PDE.Dirichlet.coordinateVector (fun p q x => OAI.Analysis.Calculus.Quaternion.realCoefficients e (A x) p q) v p x)) :
    (∫ x in euclideanLatticeCell c L a b ∩ {x | r x < 0},
      u x * OAI.LinearAlgebra.Moore.realTrace (A x * OAI.Analysis.PDE.Dirichlet.quaternionHessian e v x)) =
    -(∫ x in euclideanLatticeCell c L a b ∩ {x | r x < 0},
      ∑ p, ∑ q, OAI.Analysis.Calculus.Quaternion.realCoefficients e (A x) p q * OAI.Analysis.PDE.Dirichlet.realGradient u x p * OAI.Analysis.PDE.Dirichlet.realGradient v x q) := by
  have hK (p q : Fin n × Fin s) :
      ContDiff ℝ 1 (fun x => OAI.Analysis.Calculus.Quaternion.realCoefficients e (A x) p q) :=
    (OAI.Analysis.PDE.Green.realCoefficientCLM e p q).contDiff.comp hA
  have hd (x : OAI.Analysis.PDE.Dirichlet.CoordinateSpace n s) (q : Fin n × Fin s) :
      (∑ p, fderiv ℝ (fun y => OAI.Analysis.Calculus.Quaternion.realCoefficients e (A y) p q) x (OAI.Analysis.PDE.Dirichlet.coordinateVector p)) = 0 := by
    simp_rw [OAI.Analysis.PDE.Green.fderiv_realCoefficient e _ _ (hA.differentiable (by norm_num) x)]
    exact OAI.Analysis.Calculus.Quaternion.realCoefficients_divergence_zero e _ (hdiv x) q
  have h := real_operator_first_green_lattice c L a b hab
    (fun p q x => OAI.Analysis.Calculus.Quaternion.realCoefficients e (A x) p q) hK hu hv hr hd hrne huz hface
  have hform (x : OAI.Analysis.PDE.Dirichlet.CoordinateSpace n s) :
      OAI.LinearAlgebra.Moore.realTrace (A x * OAI.Analysis.PDE.Dirichlet.quaternionHessian e v x) =
      ∑ p, ∑ q, OAI.Analysis.Calculus.Quaternion.realCoefficients e (A x) p q * OAI.Analysis.PDE.Dirichlet.realHessian v x p q :=
    OAI.Analysis.PDE.Green.realTrace_hessianMap (A x) e (OAI.Analysis.PDE.Dirichlet.realHessian v x) (OAI.Analysis.PDE.Dirichlet.realHessian_isSymm hv.contDiffAt)
  simpa only [hform, OAI.Analysis.PDE.Dirichlet.realHessian, OAI.Analysis.PDE.Dirichlet.realGradient, OAI.Analysis.PDE.Dirichlet.coordinateVector] using h

theorem real_operator_second_green_lattice
    {ι : Type*} [Fintype ι] [DecidableEq ι] {m : ℕ} (c : ι ≃ Fin (m + 1))
    (L : (Fin (m + 1) → ℝ) ≃L[ℝ] (Fin (m + 1) → ℝ))
    (a b : Fin (m + 1) → ℝ) (hab : a ≤ b)
    (K : ι → ι → EuclideanSpace ℝ ι → ℝ) {r u v : EuclideanSpace ℝ ι → ℝ}
    (hK : ∀ i j, ContDiff ℝ 1 (K i j))
    (hu : ContDiff ℝ 2 u) (hv : ContDiff ℝ 2 v) (hr : ContDiff ℝ 2 r)
    (hKs : ∀ i j x, K i j x = K j i x)
    (hdiv : ∀ x j, ∑ i, fderiv ℝ (K i j) x (EuclideanSpace.single i 1) = 0)
    (hrne : ∀ x ∈ euclideanLatticeCell c L a b, r x = 0 → fderiv ℝ r x ≠ 0)
    (huz : ∀ x, r x = 0 → u x = 0)
    (hnormal : ∀ x, r x = 0 →
      (∑ i, ∑ j, K i j x * (fderiv ℝ r x (EuclideanSpace.single i 1) *
        fderiv ℝ r x (EuclideanSpace.single j 1))) = 0)
    (hface : CompatibleLatticeFaces c L a b r
      (OAI.Analysis.PDE.Green.secondGreenFlux (fun i => EuclideanSpace.single i 1) K u v)) :
    (∫ x in euclideanLatticeCell c L a b ∩ {x | r x < 0}, u x *
      (∑ i, ∑ j, K i j x * fderiv ℝ (fderiv ℝ v) x
        (EuclideanSpace.single i 1) (EuclideanSpace.single j 1))) =
    ∫ x in euclideanLatticeCell c L a b ∩ {x | r x < 0}, v x *
      (∑ i, ∑ j, K i j x * fderiv ℝ (fderiv ℝ u) x
        (EuclideanSpace.single i 1) (EuclideanSpace.single j 1)) := by
  let d : ι → EuclideanSpace ℝ ι := fun i => EuclideanSpace.single i 1
  have hb := (isBounded_euclideanLatticeCell c L a b).subset
    (inter_subset_left : (euclideanLatticeCell c L a b ∩ {x | r x < 0}) ⊆ _)
  have hvF := OAI.Analysis.PDE.Green.contDiff_realFlux d K hK hv
  have huF := OAI.Analysis.PDE.Green.contDiff_realFlux d K hK hu
  have hvi : IntegrableOn (fun x => u x * ∑ i, fderiv ℝ (OAI.Analysis.PDE.Green.realFlux d K v i) x (d i))
      (euclideanLatticeCell c L a b ∩ {x | r x < 0}) :=
    OAI.Analysis.PDE.Energy.continuous_integrableOn_bounded hb (hu.continuous.mul
      (continuous_finsetSum _ (fun i _ => OAI.Analysis.PDE.Green.continuous_directional (hvF i) (d i))))
  have hui : IntegrableOn (fun x => v x * ∑ i, fderiv ℝ (OAI.Analysis.PDE.Green.realFlux d K u i) x (d i))
      (euclideanLatticeCell c L a b ∩ {x | r x < 0}) :=
    OAI.Analysis.PDE.Energy.continuous_integrableOn_bounded hb (hv.continuous.mul
      (continuous_finsetSum _ (fun i _ => OAI.Analysis.PDE.Green.continuous_directional (huF i) (d i))))
  have he := integral_divergence_euclidean_lattice_zero c L a b hab (OAI.Analysis.PDE.Green.secondGreenFlux d K u v)
    (OAI.Analysis.PDE.Green.contDiff_secondGreenFlux d K hK hu hv) hr hrne
    (OAI.Analysis.PDE.Green.secondGreenFlux_tangent d K hr hu huz hnormal) hface
  change (∫ x in euclideanLatticeCell c L a b ∩ {x | r x < 0},
    ∑ i, fderiv ℝ (OAI.Analysis.PDE.Green.secondGreenFlux d K u v i) x (d i)) = 0 at he
  simp_rw [OAI.Analysis.PDE.Green.secondGreenFlux_divergence d K hK hu hv hKs] at he
  rw [integral_sub hvi hui] at he
  have heq := sub_eq_zero.mp he
  simpa only [OAI.Analysis.PDE.Green.realFlux_divergence d K hK hv hdiv,
    OAI.Analysis.PDE.Green.realFlux_divergence d K hK hu hdiv] using heq

end OAI.Analysis.PDE.Concentration

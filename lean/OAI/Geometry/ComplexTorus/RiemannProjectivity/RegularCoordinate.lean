import OAI.Geometry.ComplexTorus.RiemannProjectivity.PolynomialSimple
import OAI.Geometry.ComplexTorus.RiemannProjectivity.GlobalEquation
import OAI.AlgebraicGeometry.ComplexPoints.Analytic.PolynomialDerivative

/-! # Regular Coordinate -/

namespace OAI.Geometry.ComplexTorus.RiemannProjectivity.RegularCoordinate.Constructions.RegularCoordinateDerivative

noncomputable section

/-! # RiemannProjectivity: an algebraic coordinate equation is nonsingular at an isolated inverse branch -/

open Set _root_.Polynomial _root_.Metric

variable {X : Type*} [TopologicalSpace X] {d k : ℕ}

theorem derivative_ne_zero {f : X → (Fin (d + 1) → ℂ)} (hf : IsClosedMap f)
    {l : X → ℂ} (hl : Continuous l)
    (e : OpenPartialHomeomorph X (Fin (d + 1) → ℂ)) (he : (e : X → (Fin (d + 1) → ℂ)) = f)
    {x : X} (hx : x ∈ e.source) (hx0 : f x ≠ 0) (hfinite : (f ⁻¹' {f x}).Finite)
    (hsep : ∀ u, f u = f x → l u = l x → u = x)
    (F : Polynomial (MvPolynomial (Fin (d + 1)) ℂ))
    (hF : ∀ y, (F.map (MvPolynomial.eval y)).Monic ∧
      (F.map (MvPolynomial.eval y)).natDegree = k)
    (hgen : GlobalEquation.Constructions.GlobalMonicEquation.GenericallySeparable F)
    (hroots : ∀ y z, (y, z) ∈ range (fun u => (f u, l u)) ↔
      F.eval₂ (MvPolynomial.eval y) z = 0) :
    (F.map (MvPolynomial.eval (f x))).derivative.eval (l x) ≠ 0 := by
  obtain ⟨R, O, g, hR, hO, hxO, _, hg, heq⟩ :=
    PolynomialSimple.Constructions.LocalCoordinateGraph.exists_graph hf hl e he hx hfinite hsep
  let P : (Fin (d + 1) → ℂ) → ℂ[X] := fun y => F.map (MvPolynomial.eval y)
  have hcoeff (j : ℕ) : DifferentiableOn ℂ (fun y => (P y).coeff j) univ := by
    simpa only [P, coeff_map] using (AlgebraicGeometry.ComplexPoints.Analytic.PolynomialDerivative.differentiable_polynomial_eval (F.coeff j)).differentiableOn
  have hdiff : DifferentiableOn ℂ (fun p : (Fin (d + 1) → ℂ) × ℂ => (P p.1).eval p.2)
      (O ×ˢ univ) :=
    ParameterEquationsOn.Constructions.ParameterEquations.differentiableOn_eval k (fun y => (hF y).2.le) hcoeff
      differentiable_fst.differentiableOn differentiable_snd.differentiableOn (fun _ _ => mem_univ _)
  have hzero (y : Fin (d + 1) → ℂ) (hy : y ∈ O) (z : ℂ) (hz : z ∈ closedBall (l x) R) :
      (P y).eval z = 0 ↔ z = g y := by
    change (F.map (MvPolynomial.eval y)).eval z = 0 ↔ z = g y
    rw [eval_map]
    exact (hroots y z).symm.trans (heq y hy z hz)
  have hvalue : l x = g (f x) :=
    (heq (f x) hxO (l x) (mem_closedBall_self hR.le)).mp ⟨x, rfl⟩
  have hder := PolynomialSimple.Constructions.SimpleBranch.derivative_ne_zero hO hdiff hxO hR g hg hzero (hgen (f x) hx0)
  simpa only [← hvalue] using hder

end

end OAI.Geometry.ComplexTorus.RiemannProjectivity.RegularCoordinate.Constructions.RegularCoordinateDerivative

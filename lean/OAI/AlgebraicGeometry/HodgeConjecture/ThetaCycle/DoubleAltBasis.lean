import OAI.RepresentationTheory.Theta.Kernel.Calculus

/-! # Double Alt Basis -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.DoubleAltBasis.CM

noncomputable section

/-! ThetaCycle: ThetaKernel's literal double alternation transforms by the determinant
of a two-dimensional multiplicity basis, for every bilinear tensor. -/

open scoped Classical
open OAI.RepresentationTheory.Theta.Kernel.Calculus

theorem double_alt_basis_bilinear {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]
    (Q : V →L[ℂ] V →L[ℂ] ℂ) (B : Matrix (Fin 2) (Fin 2) ℂ)
    (u : Fin 2 × Fin 2 → V) :
    RepresentationTheory.Theta.Kernel.Calculus.doubleAlt (fun a b => Q (∑ k : Fin 2, B a.2 k • u (a.1, k))
      (∑ k : Fin 2, B b.2 k • u (b.1, k))) =
      B.det * RepresentationTheory.Theta.Kernel.Calculus.doubleAlt (fun a b => Q (u a) (u b)) := by
  simp only [RepresentationTheory.Theta.Kernel.Calculus.doubleAlt, Fin.sum_univ_two, map_add, map_smul, _root_.add_apply,
    _root_.smul_apply, smul_eq_mul, Matrix.det_fin_two]
  ring

theorem double_alt_basis_hessian {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]
    (H : V [×2]→L[ℂ] ℂ) (B : Matrix (Fin 2) (Fin 2) ℂ)
    (u : Fin 2 × Fin 2 → V) :
    RepresentationTheory.Theta.Kernel.Calculus.doubleAlt (fun a b => H ![∑ k : Fin 2, B a.2 k • u (a.1, k),
      ∑ k : Fin 2, B b.2 k • u (b.1, k)]) =
      B.det * RepresentationTheory.Theta.Kernel.Calculus.doubleAlt (fun a b => H ![u a, u b]) := by
  let Q : V →L[ℂ] V →L[ℂ] ℂ :=
    (continuousMultilinearCurryFin1 ℂ V ℂ : (V [×1]→L[ℂ] ℂ) →L[ℂ] V →L[ℂ] ℂ).comp H.curryLeft
  have hQ (x y : V) : Q x y = H ![x, y] := by
    change continuousMultilinearCurryFin1 ℂ V ℂ (H.curryLeft x) y = _
    simp only [continuousMultilinearCurryFin1_apply, ContinuousMultilinearMap.curryLeft_apply]
    congr 1
    ext i
    fin_cases i <;> rfl
  simpa only [hQ] using double_alt_basis_bilinear Q B u

theorem double_alt_scalar (c : ℂ) (h : RepresentationTheory.Theta.Kernel.Calculus.TensorCoordinates) :
    RepresentationTheory.Theta.Kernel.Calculus.doubleAlt (fun a b => c * h a b) = c * RepresentationTheory.Theta.Kernel.Calculus.doubleAlt h := by
  unfold RepresentationTheory.Theta.Kernel.Calculus.doubleAlt
  ring

end

end OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.DoubleAltBasis.CM

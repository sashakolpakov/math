import OAI.AlgebraicGeometry.FormalGeometry.Completion.PolynomialQuadratic
import OAI.AlgebraicGeometry.FormalGeometry.Completion.QuadraticSpectralStep
import Mathlib.RingTheory.Noetherian.Basic

/-! # Polynomial Height Spectrum -/

namespace OAI.AlgebraicGeometry.FormalGeometry.Completion

noncomputable section

/-! Descending the polynomial degree proves the complex eigenvalue bound
without assuming that any single Hilbert coefficient is positive definite. -/

open scoped TensorProduct

universe u

theorem PolynomialQuadratic.Construction.PolynomialQuadraticHeight.complexEigenvalue_norm_of_degree_bound (d : ℕ) :
    ∀ {G : Type u} [AddCommGroup G] [Module.Finite ℤ G]
      (q : PolynomialQuadratic.Construction.PolynomialQuadraticHeight G) (_hd : ∀ g, (q.value g).natDegree ≤ d)
      (f : G →+ G) (c : ℚ)
      (_hdegree : ∀ g, (q.value (f g)).natDegree ≤ (q.value g).natDegree)
      (_hcoeff : ∀ g j, (q.value g).natDegree ≤ j →
        (q.value (f g)).coeff j = c * (q.value g).coeff j)
      (z : ℂ) (_hz : Module.End.HasEigenvalue (f.toIntLinearMap.baseChange ℂ) z),
      ‖z‖ = Real.sqrt (c : ℝ) := by
  induction d with
  | zero =>
    intro G _ _ q hd f c _hdegree hcoeff z hz
    let Q := q.coefficientQuadratic 0 hd
    have hs (g : G) : Q.value (f g) = c * Q.value g := hcoeff g 0 (hd g)
    rcases Q.eigenvalue_kernel_or_norm f c hs z hz with hk | hnorm
    · have : Subsingleton Q.zeroKernel := q.zero_degree_kernel_subsingleton hd
      have : Subsingleton (TensorProduct ℤ ℂ Q.zeroKernel) := inferInstance
      obtain ⟨v, hv⟩ := hk.exists_hasEigenvector
      exact False.elim (hv.2 (Subsingleton.elim v 0))
    · exact hnorm
  | succ d ih =>
    intro G _ _ q hd f c hdegree hcoeff z hz
    let Q := q.coefficientQuadratic (d + 1) hd
    have hs (g : G) : Q.value (f g) = c * Q.value g := hcoeff g (d + 1) (hd g)
    rcases Q.eigenvalue_kernel_or_norm f c hs z hz with hk | hnorm
    · have : Module.Finite ℤ Q.zeroKernel := Module.Finite.of_injective
        Q.zeroKernel.subtype.toIntLinearMap Subtype.val_injective
      have hd' : ∀ g : Q.zeroKernel, ((q.restrict Q.zeroKernel).value g).natDegree ≤ d :=
        q.kernel_degree_bound d hd
      apply ih (q.restrict Q.zeroKernel) hd' (Q.kernelSimilitude f c hs) c ?_ ?_ z hk
      · intro g
        exact hdegree g
      · intro g j hg
        exact hcoeff g j hg
    · exact hnorm

end

end OAI.AlgebraicGeometry.FormalGeometry.Completion

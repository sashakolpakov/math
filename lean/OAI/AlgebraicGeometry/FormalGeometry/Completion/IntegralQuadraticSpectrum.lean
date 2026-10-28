import OAI.AlgebraicGeometry.FormalGeometry.Completion.QuadraticQuotientSimilitude
import OAI.AlgebraicGeometry.FormalGeometry.Completion.RationalSimilitudeSpectrum
import Mathlib.RingTheory.TensorProduct.Finite

/-! # Integral Quadratic Spectrum -/

namespace OAI.AlgebraicGeometry.FormalGeometry.Completion

noncomputable section

/-! The positive rational form on a finitely generated abelian group
controls the eigenvalues of its directly complexified endomorphism. -/

open scoped TensorProduct

universe u
variable {G : Type u} [AddCommGroup G]

theorem IntegralQuadraticSpectrum.Construction.eigenvalue_doubleBaseChange_of_baseChange (T : Module.End ℤ G)
    (z : ℂ) (hz : Module.End.HasEigenvalue (T.baseChange ℂ) z) :
    Module.End.HasEigenvalue ((T.baseChange ℚ).baseChange ℂ) z := by
  let e := TensorProduct.AlgebraTensorModule.cancelBaseChange ℤ ℚ ℂ ℂ G
  obtain ⟨v, hv⟩ := hz.exists_hasEigenvector
  have hev : T.baseChange ℂ v = z • v := Module.End.mem_eigenspace_iff.mp hv.1
  apply Module.End.hasEigenvalue_of_hasEigenvector (x := e.symm v)
  refine ⟨Module.End.mem_eigenspace_iff.mpr ?_, ?_⟩
  · rw [LinearMap.baseChange_baseChange]
    change e.symm (T.baseChange ℂ (e (e.symm v))) = z • e.symm v
    rw [e.apply_symm_apply, hev, map_smul]
  · intro h
    apply hv.2
    have hh := congrArg e h
    simpa using hh

theorem IntegralQuadraticSpectrum.Construction.eigenvalue_baseChange_of_doubleBaseChange (T : Module.End ℤ G)
    (z : ℂ) (hz : Module.End.HasEigenvalue ((T.baseChange ℚ).baseChange ℂ) z) :
    Module.End.HasEigenvalue (T.baseChange ℂ) z := by
  let e := TensorProduct.AlgebraTensorModule.cancelBaseChange ℤ ℚ ℂ ℂ G
  obtain ⟨v, hv⟩ := hz.exists_hasEigenvector
  have hev : (T.baseChange ℚ).baseChange ℂ v = z • v := Module.End.mem_eigenspace_iff.mp hv.1
  apply Module.End.hasEigenvalue_of_hasEigenvector (x := e v)
  refine ⟨Module.End.mem_eigenspace_iff.mpr ?_, ?_⟩
  · rw [LinearMap.baseChange_baseChange] at hev
    have h := congrArg e hev
    change e (e.symm (T.baseChange ℂ (e v))) = e (z • v) at h
    simpa only [e.apply_symm_apply, map_smul] using h
  · intro h
    apply hv.2
    exact e.injective (h.trans (map_zero e).symm)

theorem NonnegativeQuadraticMk.Construction.NonnegativeQuadratic.complexEigenvalue_norm [Module.Finite ℤ G]
    (q : NonnegativeQuadraticMk.Construction.NonnegativeQuadratic G) (hzero : ∀ g, q.value g = 0 → g = 0)
    (f : G →+ G) (c : ℚ) (hf : ∀ g, q.value (f g) = c * q.value g)
    (z : ℂ) (hz : Module.End.HasEigenvalue (f.toIntLinearMap.baseChange ℂ) z) :
    ‖z‖ = Real.sqrt (c : ℝ) :=
  RationalSimilitudeSpectrum.Construction.rationalQuadraticSimilitude_eigenvalue_norm q.rationalQuadraticForm (q.rationalQuadraticForm_posDef hzero)
    (f.toIntLinearMap.baseChange ℚ) c (q.rationalQuadraticForm_similitude f c hf) z
    (IntegralQuadraticSpectrum.Construction.eigenvalue_doubleBaseChange_of_baseChange f.toIntLinearMap z hz)

theorem NonnegativeQuadraticMk.Construction.NonnegativeQuadratic.quotientComplexEigenvalue_norm
    (q : NonnegativeQuadraticMk.Construction.NonnegativeQuadratic G) [Module.Finite ℤ (G ⧸ q.zeroKernel)]
    (f : G →+ G) (c : ℚ) (hf : ∀ g, q.value (f g) = c * q.value g)
    (z : ℂ) (hz : Module.End.HasEigenvalue ((q.quotientSimilitude f c hf).toIntLinearMap.baseChange ℂ) z) :
    ‖z‖ = Real.sqrt (c : ℝ) :=
  q.quotientQuadratic.complexEigenvalue_norm (fun g hg => (q.quotientValue_eq_zero_iff g).mp hg)
    (q.quotientSimilitude f c hf) c (q.quotientSimilitude_value f c hf) z hz

end

end OAI.AlgebraicGeometry.FormalGeometry.Completion

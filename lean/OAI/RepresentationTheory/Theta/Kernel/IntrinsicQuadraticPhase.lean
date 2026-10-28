import OAI.RepresentationTheory.Theta.Kernel.IntrinsicIntegerSupport
import OAI.RepresentationTheory.Theta.Kernel.IntrinsicRationalPhaseArithmetic
import OAI.RepresentationTheory.Theta.Kernel.IntrinsicPhaseCosets

/-! # Intrinsic Quadratic Phase -/

namespace OAI.RepresentationTheory.Theta.Kernel.IntrinsicQuadraticPhase.Intrinsic

noncomputable section

/-! Every rational quadratic phase can be absorbed into an actual native
finite-Schwartz input. Its periods are derived from compact support and
finite integer-basis denominator clearing. -/

open scoped _root_.NumberField Classical

open OAI.RepresentationTheory.Theta.Adelic.FiniteSchwartz OAI.RepresentationTheory.Theta.Adelic.Evaluation OAI.RepresentationTheory.Theta.Adelic.CompactSupport.AdelicSchwartz
open OAI.RepresentationTheory.Theta.Kernel.IntrinsicIntegerSupport.Intrinsic OAI.RepresentationTheory.Theta.Kernel.IntrinsicRationalPhaseArithmetic.Intrinsic OAI.RepresentationTheory.Theta.Kernel.IntrinsicPhaseCosets.Intrinsic

variable (F : Type) [Field F] [NumberField F] (N : ℕ)

def latticeBilinear (B : (Fin N → F) →ₗ[ℚ] (Fin N → F) →ₗ[ℚ] ℚ) (r : 𝓞 F) :
    (Fin N → 𝓞 F) →ₗ[ℤ] (Fin N → 𝓞 F) →ₗ[ℤ] ℚ :=
  LinearMap.mk₂ ℤ (fun u v => B (IntrinsicIntegerSupport.Intrinsic.scaledIntegers F N r u) (IntrinsicIntegerSupport.Intrinsic.scaledIntegers F N r v))
    (by intro u v w; rw [map_add, map_add, LinearMap.add_apply])
    (by intro c u v; simp only [map_zsmul, LinearMap.smul_apply])
    (by intro u v w; rw [map_add, map_add])
    (by intro c u v; simp only [map_zsmul])

def quadraticPhase (B : (Fin N → F) →ₗ[ℚ] (Fin N → F) →ₗ[ℚ] ℚ) (x : Fin N → F) : ℂ :=
  Complex.exp ((Real.pi : ℂ) * Complex.I * ((B x x : ℚ) : ℂ))

theorem rational_phase_eq {a b : ℚ} (h : ∃ z : ℤ, b - a = 2 * z) :
    Complex.exp ((Real.pi : ℂ) * Complex.I * (a : ℂ)) =
      Complex.exp ((Real.pi : ℂ) * Complex.I * (b : ℂ)) := by
  obtain ⟨z,hz⟩ := h
  have hb : b = a + 2 * z := by linarith
  have hc : (b : ℂ) = (a : ℂ) + 2 * z := by exact_mod_cast hb
  have he : (Real.pi : ℂ) * Complex.I * (b : ℂ) =
      (Real.pi : ℂ) * Complex.I * (a : ℂ) + (z : ℂ) * (2 * Real.pi * Complex.I) := by
    rw [hc]
    ring
  rw [he, Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, mul_one]

theorem native_quadratic_phase_period (f : Adelic.FiniteSchwartz.finiteSchwartz F N)
    (B : (Fin N → F) →ₗ[ℚ] (Fin N → F) →ₗ[ℚ] ℚ) :
    ∃ M : ℕ, ∃ hM : 0 < M,
      (∀ u ∈ Weil.AdelicSplitting.FiniteLattices.Construction.finiteAdelicPositionLattice (M : F) (by exact_mod_cast hM.ne'),
        ∀ x, Adelic.Evaluation.finiteSchwartzFunction F N f (u + x) = Adelic.Evaluation.finiteSchwartzFunction F N f x) ∧
      ∀ x y : Fin N → F,
        Adelic.Evaluation.finiteSchwartzFunction F N f (Weil.AdelicSplitting.FiniteCosets.Construction.finiteRationalPosition x) ≠ 0 →
        Weil.AdelicSplitting.FiniteCosets.Construction.finiteRationalPosition x - Weil.AdelicSplitting.FiniteCosets.Construction.finiteRationalPosition y ∈
          Weil.AdelicSplitting.FiniteLattices.Construction.finiteAdelicPositionLattice (M : F) (by exact_mod_cast hM.ne') →
        quadraticPhase F N B x = quadraticPhase F N B y := by
  obtain ⟨r,hr,hsupport⟩ := IntrinsicIntegerSupport.Intrinsic.native_support_integer_presentation F N f
  obtain ⟨M₀,hM₀,hperiod⟩ := Weil.AdelicSplitting.FiniteLattices.Construction.finite_locallyConstant_lattice_period
    (Adelic.Evaluation.finiteSchwartzFunction F N f) (Adelic.CompactSupport.AdelicSchwartz.finiteSchwartzFunction_mem F N f).1
      (Adelic.CompactSupport.AdelicSchwartz.finiteSchwartzFunction_mem F N f).2
  obtain ⟨D,hD,hden⟩ := IntrinsicRationalPhaseArithmetic.Intrinsic.bilinear_integer_denominator
    (Weil.AdelicSplitting.PositionBasis.LocalAnalysis.positionBasis N (NumberField.RingOfIntegers.basis F)) (latticeBilinear F N B r)
  let M := 2 * D * M₀
  have hM : 0 < M := by dsimp [M]; positivity
  have hdiv : M₀ ∣ M := dvd_mul_left M₀ (2 * D)
  have hlat := IntrinsicIntegerSupport.Intrinsic.lattice_nat_multiple F N M₀ M hM₀ hM hdiv
  refine ⟨M,hM,(fun u hu x => hperiod u (hlat hu) x),?_⟩
  intro x y hx hxy
  obtain ⟨u,hu⟩ := hsupport x hx
  let hMF : (M : F) ≠ 0 := by exact_mod_cast hM.ne'
  have hyx : Weil.AdelicSplitting.FiniteCosets.Construction.finiteRationalPosition (fun i => y i - x i) ∈
      Weil.AdelicSplitting.FiniteLattices.Construction.finiteAdelicPositionLattice (M : F) hMF := by
    have hn := (Weil.AdelicSplitting.FiniteLattices.Construction.finiteAdelicPositionLattice (M : F) hMF).neg_mem hxy
    have he : Weil.AdelicSplitting.FiniteCosets.Construction.finiteRationalPosition (fun i => y i - x i) =
        Weil.AdelicSplitting.FiniteCosets.Construction.finiteRationalPosition y - Weil.AdelicSplitting.FiniteCosets.Construction.finiteRationalPosition x := by
      funext i
      exact map_sub (algebraMap F (Weil.AdelicSplitting.ArchimedeanAdeles.Construction.FiniteAdeles F)) (y i) (x i)
    rw [he]
    simpa only [neg_sub] using hn
  have hv := (Weil.AdelicSplitting.FiniteLattices.Construction.rational_mem_finiteAdelicPositionLattice_iff (M : F) hMF (fun i => y i - x i)).mp hyx
  choose v hv using hv
  let w : Fin N → 𝓞 F := fun i => r * (M₀ : 𝓞 F) * v i
  have hy : IntrinsicIntegerSupport.Intrinsic.scaledIntegers F N r (u + (2 * (D : ℤ)) • w) = y := by
    rw [map_add, hu]
    change x + IntrinsicIntegerSupport.Intrinsic.scaledIntegers F N r ((2 * (D : ℤ)) • (fun i => r * (M₀ : 𝓞 F) * v i)) = y
    rw [IntrinsicIntegerSupport.Intrinsic.scaledIntegers_translation F N r hr M₀ D v]
    funext i
    have hi : (2 * D * M₀ : F) * algebraMap (𝓞 F) F (v i) = y i - x i := by
      simpa only [M, Nat.cast_mul, Nat.cast_ofNat] using hv i
    change x i + (2 * D * M₀ : F) * algebraMap (𝓞 F) F (v i) = y i
    rw [hi]
    ring
  obtain ⟨z,hz⟩ := IntrinsicRationalPhaseArithmetic.Intrinsic.quadratic_even_difference (latticeBilinear F N B r) D hden u w
  change B (IntrinsicIntegerSupport.Intrinsic.scaledIntegers F N r (u + (2 * (D : ℤ)) • w))
      (IntrinsicIntegerSupport.Intrinsic.scaledIntegers F N r (u + (2 * (D : ℤ)) • w)) -
    B (IntrinsicIntegerSupport.Intrinsic.scaledIntegers F N r u) (IntrinsicIntegerSupport.Intrinsic.scaledIntegers F N r u) = 2 * z at hz
  rw [hu, hy] at hz
  exact rational_phase_eq ⟨z,hz⟩

theorem native_quadratic_phase_input (f : Adelic.FiniteSchwartz.finiteSchwartz F N)
    (B : (Fin N → F) →ₗ[ℚ] (Fin N → F) →ₗ[ℚ] ℚ) :
    ∃ g : Adelic.FiniteSchwartz.finiteSchwartz F N, ∀ x : Fin N → F,
      Adelic.Evaluation.finiteSchwartzFunction F N g (Weil.AdelicSplitting.FiniteCosets.Construction.finiteRationalPosition x) =
        quadraticPhase F N B x * Adelic.Evaluation.finiteSchwartzFunction F N f (Weil.AdelicSplitting.FiniteCosets.Construction.finiteRationalPosition x) := by
  obtain ⟨M,hM,hperiod,hphase⟩ := native_quadratic_phase_period F N f B
  exact IntrinsicPhaseCosets.Intrinsic.native_phase_input F N f (quadraticPhase F N B) M hM hperiod hphase

end

end OAI.RepresentationTheory.Theta.Kernel.IntrinsicQuadraticPhase.Intrinsic

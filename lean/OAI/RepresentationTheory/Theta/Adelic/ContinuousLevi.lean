import OAI.RepresentationTheory.Theta.Adelic.LeviPairing
import OAI.RepresentationTheory.Weil.UnitarySplitting.Weak
import OAI.RepresentationTheory.Weil.UnitarySplitting.LocalTest

/-! # Continuous Levi -/

namespace OAI.RepresentationTheory.Theta.Adelic.ContinuousLevi

noncomputable section

/-! Strong continuity of the actual positive Levi oscillator over every
local field. Continuity of the Haar modulus is recovered from two continuous
substitution pairings and their exact adjoint relation. -/

open _root_.MeasureTheory Filter
open scoped _root_.Topology ComplexConjugate InnerProductSpace

open OAI.RepresentationTheory.Theta.Adelic.LeviPairing

variable {k : Type} [NormedField k] [LocallyCompactSpace k]
variable [MeasurableSpace k] [BorelSpace k] [SecondCountableTopology k] {N : ℕ}

theorem determinantModulus_continuous_of_test (u : Weil.Local.FunctionsMetaplectic.Construction.schwartzBruhat k N) (hu : u ≠ 0) :
    Continuous (fun A : Weil.Local.FunctionsMetaplectic.Construction.GeneralLinear k N => Weil.Local.FunctionsMetaplectic.Construction.localModulus k (Weil.Local.FunctionsMetaplectic.Construction.determinantUnit k A)) := by
  apply continuous_iff_continuousAt.mpr
  intro A₀
  let v := Weil.Local.LinearSubstitution.Construction.testSubstitution A₀ u
  have hv : v ≠ 0 := fun hz => hu ((Weil.Local.LinearSubstitution.Construction.testSubstitution A₀).injective (hz.trans (map_zero _).symm))
  let a := fun A : Weil.Local.FunctionsMetaplectic.Construction.GeneralLinear k N => LeviPairing.rawPairing A u v
  let b := fun A : Weil.Local.FunctionsMetaplectic.Construction.GeneralLinear k N => conj (LeviPairing.rawPairing A⁻¹ v u)
  have ha : Continuous a := LeviPairing.rawPairing_continuous u v
  have hb : Continuous b := ((LeviPairing.rawPairing_continuous v u).comp continuous_inv).star
  have hn : a A₀ ≠ 0 := by
    change LeviPairing.rawPairing A₀ u (Weil.Local.LinearSubstitution.Construction.testSubstitution A₀ u) ≠ 0
    rw [LeviPairing.rawPairing_self_image]
    exact inner_self_ne_zero.mpr (fun hz => hv ((Weil.UnitarySplitting.Weak.Construction.testToL2_injective k N) (hz.trans (map_zero _).symm)))
  have hbn : b A₀ ≠ 0 := by
    intro hz
    apply hn
    change LeviPairing.rawPairing A₀ u v = 0
    rw [LeviPairing.rawPairing_adjoint]
    change _ * b A₀ = 0
    rw [hz, mul_zero]
  have he (A : Weil.Local.FunctionsMetaplectic.Construction.GeneralLinear k N) (hB : b A ≠ 0) :
      (Weil.Local.FunctionsMetaplectic.Construction.localModulus k (Weil.Local.FunctionsMetaplectic.Construction.determinantUnit k A) : ℂ) = a A / b A := by
    apply (eq_div_iff hB).mpr
    exact (LeviPairing.rawPairing_adjoint A u v).symm
  have hq := ha.continuousAt.div hb.continuousAt hbn
  have hevent : (fun A : Weil.Local.FunctionsMetaplectic.Construction.GeneralLinear k N => (Weil.Local.FunctionsMetaplectic.Construction.localModulus k (Weil.Local.FunctionsMetaplectic.Construction.determinantUnit k A) : ℂ))
      =ᶠ[𝓝 A₀] (fun A => a A / b A) := by
    filter_upwards [hb.continuousAt.eventually_ne hbn] with A hA
    exact he A hA
  have hC : ContinuousAt (fun A : Weil.Local.FunctionsMetaplectic.Construction.GeneralLinear k N =>
      (Weil.Local.FunctionsMetaplectic.Construction.localModulus k (Weil.Local.FunctionsMetaplectic.Construction.determinantUnit k A) : ℂ)) A₀ :=
    hq.congr_of_eventuallyEq hevent
  exact Complex.continuous_re.continuousAt.comp hC

theorem nativeCover_continuous_of_weak {P : Type} [TopologicalSpace P]
    (ψ : AddChar k ℂ) (a : P → Weil.AdelicSplitting.Oscillator.Construction.LocalCover k N ψ)
    (hp : Continuous (fun p => Weil.AdelicSplitting.Oscillator.Construction.localProjection k N ψ (a p)))
    (hw : ∀ f h, Continuous (fun p =>
      ⟪Weil.UnitarySplitting.Weak.Construction.testToL2 k N h, Weil.UnitarySplitting.Weak.Construction.testToL2 k N (Weil.AdelicSplitting.Oscillator.Construction.localOperator k N ψ (a p) f)⟫_ℂ)) : Continuous a := by
  let A := fun p => Weil.AdelicSplitting.Oscillator.Construction.localOperator k N ψ (a p)
  have hA (p : P) (f : Weil.Local.FunctionsMetaplectic.Construction.schwartzBruhat k N) : Weil.Local.FunctionsMetaplectic.Construction.l2Energy k N (A p f) = Weil.Local.FunctionsMetaplectic.Construction.l2Energy k N f :=
    (a p).property.1 f
  have hi (p : P) (f : Weil.Local.FunctionsMetaplectic.Construction.schwartzBruhat k N) : Weil.Local.FunctionsMetaplectic.Construction.l2Energy k N ((A p).symm f) = Weil.Local.FunctionsMetaplectic.Construction.l2Energy k N f := by
    rw [← hA p ((A p).symm f), (A p).apply_symm_apply]
  apply continuous_induced_rng.mpr
  apply Continuous.prodMk hp
  apply Continuous.prodMk
  · apply continuous_pi
    rintro ⟨f, h⟩
    exact Weil.UnitarySplitting.Weak.Construction.unitaryFamily_distance_continuous A hA hw f h
  · apply continuous_pi
    rintro ⟨f, h⟩
    exact Weil.UnitarySplitting.Weak.Construction.unitaryFamily_distance_continuous (fun p => (A p).symm) hi
      (Weil.UnitarySplitting.Weak.Construction.unitaryFamily_inverse_weak_continuous A hA hw) f h

theorem localLeviHom_continuous_of_test (ψ : AddChar k ℂ)
    (u : Weil.Local.FunctionsMetaplectic.Construction.schwartzBruhat k N) (hu : u ≠ 0) : Continuous (Weil.AdelicSplitting.NormalizationLevi.Construction.localLeviHom N ψ) := by
  have hm := determinantModulus_continuous_of_test u hu
  apply nativeCover_continuous_of_weak ψ
  · change Continuous (fun A : Weil.Local.FunctionsMetaplectic.Construction.GeneralLinear k N => Weil.Local.Generators.Construction.leviSymplectic A)
    unfold Weil.Local.Generators.Construction.leviSymplectic
    fun_prop
  · intro f h
    have he (A : Weil.Local.FunctionsMetaplectic.Construction.GeneralLinear k N) :
        ⟪Weil.UnitarySplitting.Weak.Construction.testToL2 k N h, Weil.UnitarySplitting.Weak.Construction.testToL2 k N (Weil.AdelicSplitting.Oscillator.Construction.localOperator k N ψ (Weil.AdelicSplitting.NormalizationLevi.Construction.localLeviHom N ψ A) f)⟫_ℂ =
          ((Real.sqrt (Weil.Local.FunctionsMetaplectic.Construction.localModulus k (Weil.Local.FunctionsMetaplectic.Construction.determinantUnit k A)))⁻¹ : ℂ) * LeviPairing.rawPairing A f h := by
      rw [Weil.UnitarySplitting.Weak.Construction.testToL2_inner]
      change (∫ x, ((Weil.AdelicSplitting.NonarchimedeanIntertwiner.LocalAnalysis.linearOscillator ψ A).val.2 f).val x * conj (h.val x)
        ∂ Weil.UnitarySplitting.Weak.Construction.referencePositionMeasure k N) = _
      simp_rw [Weil.AdelicSplitting.NonarchimedeanIntertwiner.LocalAnalysis.linearOscillator_apply, mul_assoc]
      exact integral_const_mul _ _
    simp_rw [he]
    exact ((Complex.continuous_ofReal.comp hm.sqrt).inv₀
      (fun A => Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.mpr (Weil.Local.FunctionsMetaplectic.Construction.localModulus_pos k _)).ne')).mul
      (LeviPairing.rawPairing_continuous f h)

variable [CompleteSpace k] [CharZero k]

theorem localLeviHom_continuous (hnd : ¬ DiscreteTopology k) (ψ : AddChar k ℂ) :
    Continuous (Weil.AdelicSplitting.NormalizationLevi.Construction.localLeviHom N ψ) := by
  obtain ⟨u, hu⟩ := Weil.UnitarySplitting.LocalTest.Construction.exists_test_nonzero k hnd N
  exact localLeviHom_continuous_of_test ψ u hu

def continuousLevi (hnd : ¬ DiscreteTopology k) (ψ : AddChar k ℂ) :
    Weil.Local.FunctionsMetaplectic.Construction.GeneralLinear k N →ₜ* Weil.AdelicSplitting.Oscillator.Construction.LocalCover k N ψ :=
  { Weil.AdelicSplitting.NormalizationLevi.Construction.localLeviHom N ψ with continuous_toFun := localLeviHom_continuous hnd ψ }

end

end OAI.RepresentationTheory.Theta.Adelic.ContinuousLevi

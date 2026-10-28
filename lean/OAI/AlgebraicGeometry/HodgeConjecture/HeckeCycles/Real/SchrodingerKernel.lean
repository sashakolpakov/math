import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Real.SchrodingerAction
import OAI.RepresentationTheory.Weil.Local.RealBareKernel

/-! # Schrodinger Kernel -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Real.SchrodingerKernel.CM

noncomputable section

/-! The transported real action is faithful together with its
symplectic projection, and its kernel consists exactly of the genuine
central signs. No cover or nonzero test vector is assumed. -/

open scoped Classical
open OAI.RepresentationTheory.Weil.Local.RealBareKernel.Construction
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Real.SchwartzComparison.CM
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Real.SchrodingerAction.CM

theorem faithful (n : ℕ) : Function.Injective (fun g : SchrodingerAction.CM.RealMp n => (SchrodingerAction.CM.projection n g, SchrodingerAction.CM.action n g)) := by
  intro g h he
  apply Subtype.ext
  apply Subtype.ext
  apply Prod.ext
  · have hp := congrArg (fun p => p.1) he
    have hi : Function.Injective (RepresentationTheory.Hecke.RadialDilation.SymplecticSwap.Realization.symplecticSwapHom (ι := Fin n) (K := ℝ)) :=
      Function.LeftInverse.injective SchrodingerAction.CM.swap_involutive
    exact hi hp
  · apply LinearEquiv.ext
    intro f
    have ha := congrArg (fun p => p.2) he
    have ht := congrArg (fun U : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.realSchwartz (Fin n) ≃ₗ[ℂ] RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.realSchwartz (Fin n) =>
      SchwartzComparison.CM.tests n (U ((SchwartzComparison.CM.tests n).symm f))) ha
    change RepresentationTheory.Weil.Local.FunctionsMetaplectic.Construction.weilRepresentation ℝ n (RepresentationTheory.Weil.Local.Gaussian.Construction.realCharacter 1) g f =
      RepresentationTheory.Weil.Local.FunctionsMetaplectic.Construction.weilRepresentation ℝ n (RepresentationTheory.Weil.Local.Gaussian.Construction.realCharacter 1) h f
    exact ht

def negOne (n : ℕ) : SchrodingerAction.CM.RealMp n := RepresentationTheory.Weil.Local.FunctionsMetaplectic.Construction.metaplecticMinus ℝ n (RepresentationTheory.Weil.Local.Gaussian.Construction.realCharacter 1)

theorem project_negOne (n : ℕ) : SchrodingerAction.CM.projection n (negOne n) = 1 := by
  change RepresentationTheory.Hecke.RadialDilation.SymplecticSwap.Realization.symplecticSwapHom (RepresentationTheory.Weil.Local.FunctionsMetaplectic.Construction.metaplecticProjection ℝ n (RepresentationTheory.Weil.Local.Gaussian.Construction.realCharacter 1) (RepresentationTheory.Weil.Local.FunctionsMetaplectic.Construction.metaplecticMinus ℝ n (RepresentationTheory.Weil.Local.Gaussian.Construction.realCharacter 1))) = 1
  rw [RepresentationTheory.Weil.Local.FunctionsMetaplectic.Construction.metaplecticMinus_projection, map_one]

theorem genuine (n : ℕ) (f : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.realSchwartz (Fin n)) : SchrodingerAction.CM.action n (negOne n) f = -f := by
  change (SchwartzComparison.CM.tests n).symm (RepresentationTheory.Weil.Local.FunctionsMetaplectic.Construction.weilRepresentation ℝ n (RepresentationTheory.Weil.Local.Gaussian.Construction.realCharacter 1) (RepresentationTheory.Weil.Local.FunctionsMetaplectic.Construction.metaplecticMinus ℝ n (RepresentationTheory.Weil.Local.Gaussian.Construction.realCharacter 1))
    (SchwartzComparison.CM.tests n f)) = -f
  rw [RepresentationTheory.Weil.Local.FunctionsMetaplectic.Construction.metaplecticMinus_action, map_neg, LinearEquiv.symm_apply_apply]

theorem kernel (n : ℕ) (g : SchrodingerAction.CM.RealMp n) : SchrodingerAction.CM.projection n g = 1 ↔ g = 1 ∨ g = negOne n := by
  constructor
  · intro hg
    have hp : RepresentationTheory.Weil.Local.FunctionsMetaplectic.Construction.metaplecticProjection ℝ n (RepresentationTheory.Weil.Local.Gaussian.Construction.realCharacter 1) g = 1 := by
      have h := congrArg (RepresentationTheory.Hecke.RadialDilation.SymplecticSwap.Realization.symplecticSwapHom (ι := Fin n) (K := ℝ)) hg
      change RepresentationTheory.Hecke.RadialDilation.SymplecticSwap.Realization.symplecticSwapHom (RepresentationTheory.Hecke.RadialDilation.SymplecticSwap.Realization.symplecticSwapHom (RepresentationTheory.Weil.Local.FunctionsMetaplectic.Construction.metaplecticProjection ℝ n (RepresentationTheory.Weil.Local.Gaussian.Construction.realCharacter 1) g)) =
        RepresentationTheory.Hecke.RadialDilation.SymplecticSwap.Realization.symplecticSwapHom 1 at h
      rwa [SchrodingerAction.CM.swap_involutive, map_one] at h
    obtain ⟨ε, hε, hact⟩ := RepresentationTheory.Weil.Local.RealStandardBareKernel.Construction.real_standard_metaplectic_kernel_sign g hp
    have ha (f : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.realSchwartz (Fin n)) : SchrodingerAction.CM.action n g f = ε • f := by
      apply (SchwartzComparison.CM.tests n).injective
      change RepresentationTheory.Weil.Local.FunctionsMetaplectic.Construction.weilRepresentation ℝ n (RepresentationTheory.Weil.Local.Gaussian.Construction.realCharacter 1) g (SchwartzComparison.CM.tests n f) = SchwartzComparison.CM.tests n (ε • f)
      rw [map_smul]
      exact hact (SchwartzComparison.CM.tests n f)
    rcases sq_eq_one_iff.mp hε with hε | hε
    · left
      apply faithful n
      change (SchrodingerAction.CM.projection n g, SchrodingerAction.CM.action n g) = (SchrodingerAction.CM.projection n 1, SchrodingerAction.CM.action n 1)
      apply Prod.ext
      · simpa only [map_one] using hg
      · apply LinearEquiv.ext
        intro f
        rw [ha, hε, one_smul, map_one]
        rfl
    · right
      apply faithful n
      change (SchrodingerAction.CM.projection n g, SchrodingerAction.CM.action n g) = (SchrodingerAction.CM.projection n (negOne n), SchrodingerAction.CM.action n (negOne n))
      apply Prod.ext
      · rw [hg, project_negOne]
      · apply LinearEquiv.ext
        intro f
        rw [ha, hε, genuine]
        exact neg_one_smul ℂ f
  · rintro (rfl | rfl)
    · exact map_one _
    · exact project_negOne n

theorem exists_nonzero_test (n : ℕ) : ∃ f : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.realSchwartz (Fin n), f ≠ 0 := by
  by_contra h
  push Not at h
  have hf (f : RepresentationTheory.Weil.Local.FunctionsMetaplectic.Construction.schwartzBruhat ℝ n) : f = 0 := by
    have he := congrArg (SchwartzComparison.CM.tests n) (h ((SchwartzComparison.CM.tests n).symm f))
    simpa only [LinearEquiv.apply_symm_apply, map_zero] using he
  have hr : Set.range (RepresentationTheory.Weil.Local.UnitaryInner.Construction.testToL2 ℝ n) ⊆ ({0} : Set (MeasureTheory.Lp ℂ 2 (RepresentationTheory.Weil.Local.UnitaryInner.Construction.referencePositionMeasure ℝ n))) := by
    rintro _ ⟨f, rfl⟩
    rw [hf f, map_zero]
    exact Set.mem_singleton 0
  have hm := closure_mono hr ((RepresentationTheory.Weil.Local.RealOscillator.Construction.real_testToL2_dense n) (RepresentationTheory.Weil.Local.SiegelGaussian.Construction.standardPositiveFrame n).gaussianLp)
  rw [isClosed_singleton.closure_eq] at hm
  exact (RepresentationTheory.Weil.Local.SiegelGaussian.Construction.standardPositiveFrame n).gaussianLp_ne_zero hm

theorem negOne_ne_one (n : ℕ) : negOne n ≠ 1 := by
  intro h
  obtain ⟨f, hf⟩ := exists_nonzero_test n
  have he := genuine n f
  rw [h, map_one] at he
  have hz : f = 0 := by
    apply Subtype.ext
    funext x
    have hx := congrArg (fun t : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.realSchwartz (Fin n) => t.val x) he
    exact CharZero.eq_neg_self_iff.mp hx
  exact hf hz

end

end OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Real.SchrodingerKernel.CM

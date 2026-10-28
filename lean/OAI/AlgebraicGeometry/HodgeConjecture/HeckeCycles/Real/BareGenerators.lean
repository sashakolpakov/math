import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Real.SchrodingerAction
import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Real.Fourier
import OAI.RepresentationTheory.Weil.Local.RealFourierFamily
import OAI.RepresentationTheory.Hecke.RadialDilation.QuadraticCommutator

/-! # Bare Generators -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Real.BareGenerators.CM

noncomputable section

/-! Actual real bare upper and lower generators in PoissonAutomorphy's convention,
with the exact Fourier-conjugation formula for the lower action. -/

open scoped Classical _root_.Matrix
open _root_.Matrix OAI.RepresentationTheory.Weil.Local.RealFourierFamily.Construction
open OAI.RepresentationTheory.Hecke.RadialDilation.QuadraticCommutator.Realization
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Real.SchwartzComparison.CM
variable (n : ℕ)

def upper (B : RepresentationTheory.Weil.Local.FunctionsMetaplectic.Construction.SymmetricMatrix ℝ n) : SchrodingerAction.CM.RealMp n :=
  RepresentationTheory.Weil.Local.QuadraticIntertwiner.Construction.realQuadraticMetaplectic 1 B

theorem upper_projection (B : RepresentationTheory.Weil.Local.FunctionsMetaplectic.Construction.SymmetricMatrix ℝ n) :
    SchrodingerAction.CM.projection n (upper n B) = RepresentationTheory.Hecke.RadialDilation.QuadraticCommutator.Realization.ringUpper B.val B.property := by
  change RepresentationTheory.Hecke.RadialDilation.SymplecticSwap.Realization.symplecticSwapHom (RepresentationTheory.Weil.Local.FunctionsMetaplectic.Construction.metaplecticProjection ℝ n (RepresentationTheory.Weil.Local.Gaussian.Construction.realCharacter 1) (RepresentationTheory.Weil.Local.QuadraticIntertwiner.Construction.realQuadraticMetaplectic 1 B)) = _
  rw [RepresentationTheory.Weil.Local.QuadraticIntertwiner.Construction.realQuadraticMetaplectic_projection]
  apply Subtype.ext
  exact RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.e23_quadratic_coordinates B.val

theorem upper_apply (B : RepresentationTheory.Weil.Local.FunctionsMetaplectic.Construction.SymmetricMatrix ℝ n) (f : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.realSchwartz (Fin n)) (x : Fin n → ℝ) :
    (SchrodingerAction.CM.action n (upper n B) f).val x =
      RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.standardRealCharacter (RepresentationTheory.Hecke.RadialDilation.QuadraticCommutator.Realization.ringQuadratic B.val x) * f.val x := by
  rw [SchrodingerAction.CM.action_apply]
  change (RepresentationTheory.Weil.Local.FunctionsMetaplectic.Construction.weilRepresentation ℝ n (RepresentationTheory.Weil.Local.Gaussian.Construction.realCharacter 1) (RepresentationTheory.Weil.Local.QuadraticIntertwiner.Construction.realQuadraticMetaplectic 1 B) (SchwartzComparison.CM.tests n f)).val x = _
  rw [RepresentationTheory.Weil.Local.QuadraticIntertwiner.Construction.realQuadraticMetaplectic_apply, SchwartzComparison.CM.standard_character]
  congr 1
  rw [RepresentationTheory.Weil.Local.QuadraticIntertwiner.Construction.quadratic_eq_dot]
  simp [RepresentationTheory.Hecke.RadialDilation.QuadraticCommutator.Realization.ringQuadratic, RepresentationTheory.Weil.Local.FunctionsMetaplectic.Construction.dot, dotProduct, div_eq_mul_inv, mul_comm]

def fullFourier : RepresentationTheory.Weil.Local.FunctionsMetaplectic.Construction.Oscillator ℝ n (RepresentationTheory.Weil.Local.Gaussian.Construction.realCharacter 1) :=
  RepresentationTheory.Weil.Local.RealFourierFamily.Construction.realFourierOscillatorFamily n 1 (by norm_num)

theorem fullFourier_action : (fullFourier n).val.2 = RepresentationTheory.Weil.Local.RealFourierLp.Construction.realBruhatFourier n := by
  apply LinearEquiv.ext
  intro f
  apply Subtype.ext
  funext x
  change (RepresentationTheory.Weil.Local.RealFourierFamily.Construction.realFourierScale n 1 : ℂ) * (RepresentationTheory.Weil.Local.RealFourierLp.Construction.realBruhatFourier n f).val ((1 : ℝ) • x) = _
  simp [RepresentationTheory.Weil.Local.RealFourierFamily.Construction.realFourierScale]

def lower (B : RepresentationTheory.Weil.Local.FunctionsMetaplectic.Construction.SymmetricMatrix ℝ n) : SchrodingerAction.CM.RealMp n := by
  let u := upper n ⟨-B.val, B.property.neg⟩
  let w := fullFourier n
  refine ⟨w⁻¹ * u.val * w, ?_⟩
  have h := (inferInstance : (RepresentationTheory.Weil.Local.FunctionsMetaplectic.Construction.metaplecticSubgroup ℝ n (RepresentationTheory.Weil.Local.Gaussian.Construction.realCharacter 1)).Normal).conj_mem
    u.val u.property w⁻¹
  simpa only [inv_inv] using h

theorem lower_projection (B : RepresentationTheory.Weil.Local.FunctionsMetaplectic.Construction.SymmetricMatrix ℝ n) :
    SchrodingerAction.CM.projection n (lower n B) = RepresentationTheory.Weil.Local.Generators.Construction.quadraticSymplectic B := by
  have h : RepresentationTheory.Weil.Local.FunctionsMetaplectic.Construction.metaplecticProjection ℝ n (RepresentationTheory.Weil.Local.Gaussian.Construction.realCharacter 1) (lower n B) = RepresentationTheory.Weil.Local.GenerationSymplectic.Construction.upperSymplectic B := by
    change RepresentationTheory.Weil.Local.OscillatorProjection.Construction.oscillatorProjection ℝ n (RepresentationTheory.Weil.Local.Gaussian.Construction.realCharacter 1)
      ((fullFourier n)⁻¹ * (upper n ⟨-B.val, B.property.neg⟩).val * fullFourier n) = _
    rw [map_mul, map_mul, map_inv]
    exact (RepresentationTheory.Weil.Local.OscillatorProjection.Construction.upper_quadratic_conjugation ℝ n B).symm
  change RepresentationTheory.Hecke.RadialDilation.SymplecticSwap.Realization.symplecticSwapHom (RepresentationTheory.Weil.Local.FunctionsMetaplectic.Construction.metaplecticProjection ℝ n (RepresentationTheory.Weil.Local.Gaussian.Construction.realCharacter 1) (lower n B)) = _
  rw [h]
  apply Subtype.ext
  exact RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.coordinateSwap_conjugation 1 B.val 0 1

theorem lower_action (B : RepresentationTheory.Weil.Local.FunctionsMetaplectic.Construction.SymmetricMatrix ℝ n) :
    SchrodingerAction.CM.action n (lower n B) =
      (Fourier.CM.fourierEquiv n)⁻¹ *
        SchrodingerAction.CM.action n (upper n ⟨-B.val, B.property.neg⟩) *
          Fourier.CM.fourierEquiv n := by
  apply LinearEquiv.ext
  intro f
  apply (SchwartzComparison.CM.tests n).injective
  change (fullFourier n).val.2.symm
    (RepresentationTheory.Weil.Local.FunctionsMetaplectic.Construction.weilRepresentation ℝ n (RepresentationTheory.Weil.Local.Gaussian.Construction.realCharacter 1) (upper n ⟨-B.val, B.property.neg⟩)
      ((fullFourier n).val.2 (SchwartzComparison.CM.tests n f))) = _
  rw [fullFourier_action]
  change (RepresentationTheory.Weil.Local.RealFourierLp.Construction.realBruhatFourier n).symm
    (RepresentationTheory.Weil.Local.FunctionsMetaplectic.Construction.weilRepresentation ℝ n (RepresentationTheory.Weil.Local.Gaussian.Construction.realCharacter 1) (upper n ⟨-B.val, B.property.neg⟩)
      (RepresentationTheory.Weil.Local.RealFourierLp.Construction.realBruhatFourier n (SchwartzComparison.CM.tests n f))) =
    SchwartzComparison.CM.tests n ((Fourier.CM.fourierEquiv n).symm
      (SchrodingerAction.CM.action n (upper n ⟨-B.val, B.property.neg⟩)
        (Fourier.CM.fourierEquiv n f)))
  simp [Fourier.CM.fourierEquiv, SchrodingerAction.CM.action]

end

end OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Real.BareGenerators.CM

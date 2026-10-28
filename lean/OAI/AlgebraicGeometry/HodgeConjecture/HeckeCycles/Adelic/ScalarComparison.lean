import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.OscillatorScalarComparison
import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Constructed.ConstructedAdelicGroup
import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Finite.CoverFields

/-! # Scalar Comparison -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Adelic.ScalarComparison.CM

noncomputable section

/-! Compare an actual adelic lift with a real–finite pair of actual
oscillator operators using their identical projected matrices. -/

open scoped Classical _root_.Matrix
open _root_.Matrix
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Real.SchwartzComparison.CM
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Constructed.ConstructedAdelicGroup.CM
variable (n : ℕ)

abbrev RealOscillator := RepresentationTheory.Weil.Local.FunctionsMetaplectic.Construction.Oscillator ℝ n (RepresentationTheory.Weil.Local.Gaussian.Construction.realCharacter 1)
abbrev FiniteOscillator := Finite.FiniteOscillator.CM.Oscillator (I := Fin n)

def realOperator (a : RealOscillator n) : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.realSchwartz (Fin n) ≃ₗ[ℂ] RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.realSchwartz (Fin n) :=
  (Real.SchwartzComparison.CM.tests n).trans (a.val.2.trans (Real.SchwartzComparison.CM.tests n).symm)

def pairOperator (a : RealOscillator n) (b : FiniteOscillator n) :
    RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.adelicSchwartz (Fin n) ≃ₗ[ℂ] RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.adelicSchwartz (Fin n) :=
  ProductOperators.CM.operator (realOperator n a, Finite.FiniteOscillator.CM.action b)

def pairMatrix (a : RealOscillator n) (b : FiniteOscillator n) :
    Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQ :=
  SymplecticProduct.CM.pairMatrix
    (RepresentationTheory.Hecke.RadialDilation.SymplecticSwap.Realization.symplecticSwapHom (RepresentationTheory.Weil.Local.OscillatorProjection.Construction.oscillatorProjection ℝ n (RepresentationTheory.Weil.Local.Gaussian.Construction.realCharacter 1) a)).val
    (Finite.FiniteOscillator.CM.projection b).val

theorem real_scalar (r : Constructed.ConstructedAdelicGroup.CM.RealGroup n) (a : RealOscillator n)
    (hr : (Real.SchrodingerAction.CM.projection n r).val =
      (RepresentationTheory.Hecke.RadialDilation.SymplecticSwap.Realization.symplecticSwapHom (RepresentationTheory.Weil.Local.OscillatorProjection.Construction.oscillatorProjection ℝ n (RepresentationTheory.Weil.Local.Gaussian.Construction.realCharacter 1) a)).val) :
    ∃ c : ℂ, ‖c‖ = 1 ∧ ∀ f : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.realSchwartz (Fin n),
      Real.SchrodingerAction.CM.action n r f = c • realOperator n a f := by
  have hp : RepresentationTheory.Weil.Local.OscillatorProjection.Construction.oscillatorProjection ℝ n (RepresentationTheory.Weil.Local.Gaussian.Construction.realCharacter 1) r.val = RepresentationTheory.Weil.Local.OscillatorProjection.Construction.oscillatorProjection ℝ n (RepresentationTheory.Weil.Local.Gaussian.Construction.realCharacter 1) a := by
    apply (Function.LeftInverse.injective (Real.SchrodingerAction.CM.swap_involutive (n := n)))
    exact Subtype.ext hr
  obtain ⟨c, hc, hf⟩ := OscillatorScalarComparison.CM.real n r.val a hp
  refine ⟨c, hc, ?_⟩
  intro f
  apply (Real.SchwartzComparison.CM.tests n).injective
  change r.val.val.2 (Real.SchwartzComparison.CM.tests n f) = Real.SchwartzComparison.CM.tests n (c • (Real.SchwartzComparison.CM.tests n).symm (a.val.2 (Real.SchwartzComparison.CM.tests n f)))
  rw [map_smul, LinearEquiv.apply_symm_apply]
  exact hf (Real.SchwartzComparison.CM.tests n f)

theorem finite_scalar (f : Constructed.ConstructedAdelicGroup.CM.FiniteGroup n) (b : FiniteOscillator n)
    (hf : ((Finite.ConstructedCover.CM.finiteCover (Fin n)).project f).val =
      (Finite.FiniteOscillator.CM.projection b).val) :
    ∃ c : ℂ, ‖c‖ = 1 ∧ ∀ φ : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.finiteSchwartz (Fin n),
      (Finite.ConstructedCover.CM.finiteCover (Fin n)).action f φ = c • Finite.FiniteOscillator.CM.action b φ := by
  rw [Finite.CoverFields.CM.projection_matrix] at hf
  have hp : Finite.FiniteOscillator.CM.projection f.val = Finite.FiniteOscillator.CM.projection b := Subtype.ext hf
  obtain ⟨c, hc, hφ⟩ := OscillatorScalarComparison.CM.finite f.val b hp
  refine ⟨c, hc, ?_⟩
  intro φ
  rw [Finite.CoverFields.CM.action]
  exact hφ φ

theorem scalar (g : Constructed.ConstructedAdelicGroup.CM.AdelicGroup n) (a : RealOscillator n) (b : FiniteOscillator n)
    (hg : (Constructed.ConstructedAdelicGroup.CM.projection n g).val = pairMatrix n a b) :
    ∃ c : ℂ, ‖c‖ = 1 ∧ ∀ F : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.adelicSchwartz (Fin n), Constructed.ConstructedAdelicGroup.CM.action n g F = c • pairOperator n a b F := by
  obtain ⟨⟨r, f⟩, rfl⟩ := AdelicPairGroup.CM.assemble_surjective
    (Constructed.RealCover.CM.realCover n) (Finite.ConstructedCover.CM.finiteCover (Fin n)) g
  have hr := congrArg (fun M : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQ => M.map (RingHom.fst ℝ RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQf)) hg
  have hf := congrArg (fun M : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQ => M.map (RingHom.snd ℝ RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQf)) hg
  change (SymplecticProduct.CM.pairMatrix
    ((Constructed.RealCover.CM.realCover n).project r).val
    ((Finite.ConstructedCover.CM.finiteCover (Fin n)).project f).val).map (RingHom.fst ℝ RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQf) =
      (pairMatrix n a b).map (RingHom.fst ℝ RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQf) at hr
  change (SymplecticProduct.CM.pairMatrix
    ((Constructed.RealCover.CM.realCover n).project r).val
    ((Finite.ConstructedCover.CM.finiteCover (Fin n)).project f).val).map (RingHom.snd ℝ RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQf) =
      (pairMatrix n a b).map (RingHom.snd ℝ RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQf) at hf
  rw [SymplecticProduct.CM.pairMatrix_fst, pairMatrix, SymplecticProduct.CM.pairMatrix_fst] at hr
  rw [SymplecticProduct.CM.pairMatrix_snd, pairMatrix, SymplecticProduct.CM.pairMatrix_snd] at hf
  obtain ⟨c, hc, hR⟩ := real_scalar n r a hr
  obtain ⟨d, hd, hF⟩ := finite_scalar n f b hf
  refine ⟨c * d, by rw [norm_mul, hc, hd, one_mul], ?_⟩
  have hlin : (Constructed.ConstructedAdelicGroup.CM.action n (AdelicPairGroup.CM.assemble
      (Constructed.RealCover.CM.realCover n) (Finite.ConstructedCover.CM.finiteCover (Fin n)) (r, f))).toLinearMap =
      (c * d) • (pairOperator n a b).toLinearMap := by
    apply FiniteOperators.CM.Sections.linear_ext
    intro h φ
    change AdelicPairGroup.CM.action _ _ (AdelicPairGroup.CM.assemble _ _ (r, f)) (RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.tensor h φ) = _
    rw [AdelicPairGroup.CM.action_assemble, ProductOperators.CM.operator_tensor]
    change RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.tensor (Real.SchrodingerAction.CM.action n r h)
      ((Finite.ConstructedCover.CM.finiteCover (Fin n)).action f φ) =
        (c * d) • pairOperator n a b (RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.tensor h φ)
    rw [hR, hF]
    change RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.tensor (c • realOperator n a h) (d • Finite.FiniteOscillator.CM.action b φ) =
      (c * d) • ProductOperators.CM.operator _ (RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.tensor h φ)
    rw [ProductOperators.CM.operator_tensor]
    apply Subtype.ext
    funext x
    change (c * _) * (d * _) = (c * d) * (_ * _)
    ring
  intro F
  exact LinearMap.congr_fun hlin F

end

end OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Adelic.ScalarComparison.CM

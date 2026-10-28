import OAI.AlgebraicGeometry.Crystalline.Cohomology.WittPolynomial.Evaluation
import OAI.AlgebraicGeometry.Crystalline.Cohomology.WittPolynomial.PolynomialFrameFrobenius
import OAI.AlgebraicGeometry.Crystalline.Cohomology.Polynomial.PolynomialAbsoluteFrobenius
import OAI.AlgebraicGeometry.Crystalline.Cohomology.Semilinear.CompletionDensity

/-! # Frame Frobenius Compatibility -/

namespace OAI.AlgebraicGeometry.Crystalline.Cohomology.WittPolynomial.FrameFrobeniusCompatibility.WittPolynomialFrameFrobeniusCompatibility

noncomputable section

/-! # The original completed frame comparison intertwines the actual polynomial Frobenius lift -/

open _root_.CategoryTheory

universe u

variable (p : ℕ) [Fact p.Prime] (k σ : Type u) [Field k] [CharP k p] [PerfectRing k p]
  [Fintype σ] [LinearOrder σ]

local notation "W" => WittVector p k
local notation "P" => MvPolynomial σ W
local notation "B" => MvPolynomial σ k
local notation "I" => Ideal.span {(p : W)}
local notation "r" => OAI.AlgebraicGeometry.Crystalline.Cohomology.Polynomial.AbsoluteFrobenius.PolynomialAbsoluteFrobenius.reduction p k σ
local notation "hr" => OAI.AlgebraicGeometry.Crystalline.Cohomology.WittPolynomial.Residue.WittPolynomialResidue.reduction_surjective p k σ
local notation "hb" => OAI.AlgebraicGeometry.Crystalline.Cohomology.WittPolynomial.Residue.WittPolynomialResidue.reduction_base p k σ
local notation "T" => OAI.AlgebraicGeometry.Crystalline.Cohomology.Affine.EnvelopeFrames.AffineEnvelopeFrames.frame p k B P r hr hb
local notation "Tower" => OAI.AlgebraicGeometry.Crystalline.Cohomology.Affine.EnvelopeFrames.AffineEnvelopeFrames.tower p k B P r hr hb
local notation "φ" => WittVector.frobeniusEquiv p k
local notation "F" => OAI.AlgebraicGeometry.Crystalline.Cohomology.Polynomial.AbsoluteFrobenius.PolynomialAbsoluteFrobenius.lift p k σ
local notation "Fₙ" => OAI.AlgebraicGeometry.Crystalline.Cohomology.WittPolynomial.FrameFrobenius.WittPolynomialFrameFrobenius.levelMap p k σ
local notation "q" => OAI.AlgebraicGeometry.Crystalline.Cohomology.Affine.EnvelopeFrameUniversal.AffineEnvelopeFrameUniversal.coefficient p k B P r hr hb

omit [Fintype σ] [LinearOrder σ] in
theorem levelMap_coefficient (m : ℕ) (a : P) : Fₙ m (q m a) = q m (F a) :=
  congrArg (Ideal.Quotient.mk (PadicPDP.PadicPDThickening.ideal p
    (PD.EnvelopeDp.PDEnvelope.Envelope W P I (Witt.DividedPowers.WittDividedPowers.wittDividedPowers p k) (RingHom.ker r)) m))
    (EnvelopeFrobenius.WittPolynomialEnvelopeFrobenius.map_ofAlgebra p k σ a)

omit [Fintype σ] [LinearOrder σ] in
theorem finite_naturality (m n : ℕ) (ω : DeRhamPresentationTo.DeRhamPresentation.Form W P n) :
    Evaluation.WittPolynomialEvaluation.levelMap p k σ m n ((Polynomial.AbsoluteFrobenius.PolynomialAbsoluteFrobenius.complexMap p k σ).f n ω) =
      FrameFrobenius.WittPolynomialFrameFrobenius.formsMap p k σ m n (Evaluation.WittPolynomialEvaluation.levelMap p k σ m n ω) := by
  let f : DeRhamPresentationTo.DeRhamPresentation.Form W P n →+ PD.PDDeRham.Form p k B Tower n m :=
    (Evaluation.WittPolynomialEvaluation.levelMap p k σ m n).toAddMonoidHom.comp
      ((Polynomial.AbsoluteFrobenius.PolynomialAbsoluteFrobenius.complexMap p k σ).f n).toAddMonoidHom
  let g : DeRhamPresentationTo.DeRhamPresentation.Form W P n →+ PD.PDDeRham.Form p k B Tower n m :=
    (FrameFrobenius.WittPolynomialFrameFrobenius.formsMap p k σ m n).toAddMonoidHom.comp
      (Evaluation.WittPolynomialEvaluation.levelMap p k σ m n).toAddMonoidHom
  have h : f = g := DeRhamSemilinearA.DeRhamSemilinearMap.addHom_ext W P n f g (by
    intro a v
    have hleft := (congrArg (Evaluation.WittPolynomialEvaluation.levelMap p k σ m n)
      (DeRhamSemilinearA.DeRhamSemilinearMap.formMap_symbol W W P P (φ).toRingHom F
        (Polynomial.AbsoluteFrobenius.PolynomialAbsoluteFrobenius.lift_base p k σ) n a v)).trans
          (Evaluation.WittPolynomialEvaluation.levelMap_symbol p k σ m n (F a) (F ∘ v))
    have hright := (congrArg (FrameFrobenius.WittPolynomialFrameFrobenius.formsMap p k σ m n)
      (Evaluation.WittPolynomialEvaluation.levelMap_symbol p k σ m n a v)).trans
        (FrameFrobenius.WittPolynomialFrameFrobenius.formsMap_symbol p k σ m n (q m a) (q m ∘ v))
    have hmid := congrArg₂ (PD.DeRham.PDDeRham.symbol W (T m).ring (RingHom.ker (T m).reduction) (T m).dividedPowers)
      (levelMap_coefficient p k σ m a).symm
      (funext (fun i => (levelMap_coefficient p k σ m (v i)).symm))
    exact hleft.trans (hmid.trans hright.symm))
  exact DFunLike.congr_fun h ω

def formEquiv (n : ℕ) : AdicCompletion I (DeRhamPresentationTo.DeRhamPresentation.Form W P n) ≃ₗ[W]
    PD.PDDeRham.CompletedForm p k B Tower n :=
  ((HomologicalComplex.eval (ModuleCat W) (.up ℕ) n).mapIso
    (PolynomialComplex.WittPolynomialComplex.complexIso p k σ)).toLinearEquiv

instance frame_complete (n : ℕ) : IsAdicComplete I (PD.PDDeRham.CompletedForm p k B Tower n) := by
  let : IsAdicComplete I (AdicCompletion I (DeRhamPresentationTo.DeRhamPresentation.Form W P n)) :=
    AdicCompletion.isAdicComplete (Submodule.fg_span_singleton _)
  exact NumberTheory.PadicHodge.PeriodInvariants.AdicFiniteModules.of_equiv I (formEquiv p k σ n)

theorem completed_naturality (n : ℕ) (x : AdicCompletion I (DeRhamPresentationTo.DeRhamPresentation.Form W P n)) :
    formEquiv p k σ n ((Polynomial.PolynomialAbsoluteFrobenius.completedMap p k σ).f n x) =
      PolynomialFrameFrobenius.WittPolynomialFrameFrobenius.formMap p k σ n (formEquiv p k σ n x) := by
  let f : AdicCompletion I (DeRhamPresentationTo.DeRhamPresentation.Form W P n) →ₛₗ[(φ).toRingHom]
      PD.PDDeRham.CompletedForm p k B Tower n :=
    (formEquiv p k σ n).toLinearMap.comp ((Polynomial.PolynomialAbsoluteFrobenius.completedMap p k σ).f n)
  let g : AdicCompletion I (DeRhamPresentationTo.DeRhamPresentation.Form W P n) →ₛₗ[(φ).toRingHom]
      PD.PDDeRham.CompletedForm p k B Tower n :=
    (PolynomialFrameFrobenius.WittPolynomialFrameFrobenius.formMap p k σ n).comp (formEquiv p k σ n).toLinearMap
  have h : f = g := Semilinear.CompletionDensity.SemilinearCompletionDensity.ext (φ).toRingHom I I (Submodule.fg_span_singleton _)
    (CoefficientFrobenius.WittPolynomialCoefficientFrobenius.ideal_map p k (φ).toRingHom).le f g (by
      intro a
      apply PD.PDDeRham.ext p k B Tower
      intro m
      have hf : ((Polynomial.PolynomialAbsoluteFrobenius.completedMap p k σ).f n)
          (AdicCompletion.of I (DeRhamPresentationTo.DeRhamPresentation.Form W P n) a) =
          AdicCompletion.of I (DeRhamPresentationTo.DeRhamPresentation.Form W P n) ((Polynomial.AbsoluteFrobenius.PolynomialAbsoluteFrobenius.complexMap p k σ).f n a) :=
        NumberTheory.PadicHodge.PeriodInvariants.AdicCompletionSemilinear.map_of (φ).toRingHom I I
          (CoefficientFrobenius.WittPolynomialCoefficientFrobenius.ideal_map p k (φ).toRingHom).le _ a
      have hleft := (congrArg (fun z => PD.PDDeRham.eval p k B Tower n m (formEquiv p k σ n z)) hf).trans
        (Evaluation.WittPolynomialEvaluation.eval_of p k σ m n ((Polynomial.AbsoluteFrobenius.PolynomialAbsoluteFrobenius.complexMap p k σ).f n a))
      have hright := (PolynomialFrameFrobenius.WittPolynomialFrameFrobenius.eval_formMap p k σ n m
        (formEquiv p k σ n (AdicCompletion.of I (DeRhamPresentationTo.DeRhamPresentation.Form W P n) a))).trans
          (congrArg (FrameFrobenius.WittPolynomialFrameFrobenius.formsMap p k σ m n)
            (Evaluation.WittPolynomialEvaluation.eval_of p k σ m n a))
      exact hleft.trans ((finite_naturality p k σ m n a).trans hright.symm))
  exact DFunLike.congr_fun h x

end

end OAI.AlgebraicGeometry.Crystalline.Cohomology.WittPolynomial.FrameFrobeniusCompatibility.WittPolynomialFrameFrobeniusCompatibility

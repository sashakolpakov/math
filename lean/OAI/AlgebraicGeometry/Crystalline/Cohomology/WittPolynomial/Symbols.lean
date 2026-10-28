import OAI.AlgebraicGeometry.Crystalline.Cohomology.WittPolynomial.PolynomialComplex
import OAI.AlgebraicGeometry.Crystalline.Cohomology.OrdinaryPolynomialSymbols

/-! # Symbols -/

namespace OAI.AlgebraicGeometry.Crystalline.Cohomology.WittPolynomial.Symbols.WittPolynomialSymbols

noncomputable section

/-! # The completed crystalline comparison evaluates to the original differential symbols -/

open _root_.CategoryTheory
open scoped TensorProduct

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
local notation "Tower" => OAI.AlgebraicGeometry.Crystalline.Cohomology.Affine.EnvelopeFrames.AffineEnvelopeFrames.tower p k B P r hr hb
local notation "C" => OAI.AlgebraicGeometry.Crystalline.Cohomology.PD.InverseLimit.PDInverseLimit.Ring p k B Tower
local notation "D" => OAI.AlgebraicGeometry.Crystalline.Cohomology.WittPolynomial.PolynomialComplex.WittPolynomialComplex.derivative p k σ
local notation "hD" => OAI.AlgebraicGeometry.Crystalline.Cohomology.Polynomial.FrameDifferential.PolynomialFrameDifferential.polynomial_derivatives_commute W σ
local notation "e" => OAI.AlgebraicGeometry.Crystalline.Cohomology.WittPolynomial.FrameCompletion.WittPolynomialFrameCompletion.completedEquiv p k σ
local notation "q" => OAI.AlgebraicGeometry.Crystalline.Cohomology.Affine.EnvelopeFrameUniversal.AffineEnvelopeFrameUniversal.coefficient p k B P r hr hb

theorem coordinate_of (n : ℕ) (z : Koszul.Tensor.KoszulTensor.Term W σ P n) :
    (PolynomialComplex.WittPolynomialComplex.coordinateComplexIso p k σ).hom.f n (AdicCompletion.of I _ z) =
      TensorProduct.map (e).toLinearMap (LinearMap.id : Module.End W (⋀[W]^n (σ →₀ W)))
        (TensorProduct.map (AdicCompletion.of I P) LinearMap.id z) := by
  have hI : (I).FG := Submodule.fg_span_singleton _
  have h := DFunLike.congr_fun (NumberTheory.PadicHodge.PeriodInvariants.KoszulCompletion.component_eq I hI D hD n)
    (AdicCompletion.of I (Koszul.Tensor.KoszulTensor.Term W σ P n) z)
  exact congrArg (TensorProduct.map (e).toLinearMap (LinearMap.id : Module.End W (⋀[W]^n (σ →₀ W))))
    (h.trans (NumberTheory.PadicHodge.PeriodInvariants.FiniteTensorCompletion.equiv_of I
      (NumberTheory.PadicHodge.PeriodInvariants.EquivariantKoszul.exteriorBasis (R := W) (σ := σ) n) z))

omit [CharP k p] [PerfectRing k p] [LinearOrder σ] in
theorem ordinary_inverse_symbol (n : ℕ) (a : P) (v : Fin n → σ) :
    (OrdinaryPolynomialEq.OrdinaryPolynomialCoordinates.complexIso W σ).inv.f n
      (DeRhamPresentationTo.DeRhamPresentation.symbol W P a (MvPolynomial.X ∘ v)) =
        a ⊗ₜ[W] exteriorPower.ιMulti W n (fun i => Finsupp.single (v i) 1) := by
  rw [← OrdinaryPolynomialSymbols.OrdinaryPolynomialCoordinateSymbols.hom_word]
  exact DFunLike.congr_fun
    (congrArg (fun f => (f.f n).hom) (OrdinaryPolynomialEq.OrdinaryPolynomialCoordinates.complexIso W σ).hom_inv_id) _

theorem tensor_of_symbol (n : ℕ) (a : P) (v : Fin n → σ) :
    (PolynomialComplex.WittPolynomialComplex.tensorComplexIso p k σ).hom.f n
      (AdicCompletion.of I _ (DeRhamPresentationTo.DeRhamPresentation.symbol W P a (MvPolynomial.X ∘ v))) =
        e (AdicCompletion.of I P a) ⊗ₜ[W]
          exteriorPower.ιMulti W n (fun i => Finsupp.single (v i) 1) := by
  let f : DeRhamPresentationTo.DeRhamPresentation.Form W P n →ₗ[W] Koszul.Tensor.KoszulTensor.Term W σ P n :=
    ((OrdinaryPolynomialEq.OrdinaryPolynomialCoordinates.complexIso W σ).inv.f n).hom
  let g : AdicCompletion I (Koszul.Tensor.KoszulTensor.Term W σ P n) →ₗ[W] Koszul.Tensor.KoszulTensor.Term W σ C n :=
    ((PolynomialComplex.WittPolynomialComplex.coordinateComplexIso p k σ).hom.f n).hom
  let ω : DeRhamPresentationTo.DeRhamPresentation.Form W P n := DeRhamPresentationTo.DeRhamPresentation.symbol W P a (MvPolynomial.X ∘ v)
  change g (AdicCompletion.map I f (AdicCompletion.of I (DeRhamPresentationTo.DeRhamPresentation.Form W P n) ω)) = _
  rw [AdicCompletion.map_of]
  have hf : f ω = a ⊗ₜ[W] exteriorPower.ιMulti W n (fun i => Finsupp.single (v i) 1) :=
    ordinary_inverse_symbol p k σ n a v
  rw [hf]
  exact coordinate_of p k σ n _

theorem eval_of_symbol (n m : ℕ) (a : P) (v : Fin n → σ) :
    PD.PDDeRham.eval p k B Tower n m
      ((PolynomialComplex.WittPolynomialComplex.complexIso p k σ).hom.f n
        (AdicCompletion.of I _ (DeRhamPresentationTo.DeRhamPresentation.symbol W P a (MvPolynomial.X ∘ v)))) =
      PD.DeRham.PDDeRham.symbol W (Affine.EnvelopeFrames.AffineEnvelopeFrames.frame p k B P r hr hb m).ring
        (RingHom.ker (Affine.EnvelopeFrames.AffineEnvelopeFrames.frame p k B P r hr hb m).reduction)
        (Affine.EnvelopeFrames.AffineEnvelopeFrames.frame p k B P r hr hb m).dividedPowers
        (q m a) (fun i => q m (MvPolynomial.X (v i))) := by
  change PD.PDDeRham.eval p k B Tower n m
    ((Affine.PolynomialComparison.AffinePolynomialComparison.complexIso p k B σ r hr hb).hom.f n
      ((PolynomialComplex.WittPolynomialComplex.tensorComplexIso p k σ).hom.f n
        (AdicCompletion.of I _ (DeRhamPresentationTo.DeRhamPresentation.symbol W P a (MvPolynomial.X ∘ v))))) = _
  rw [tensor_of_symbol]
  let : LinearOrder σ := LinearOrder.lift' (Fintype.equivFin σ) (Fintype.equivFin σ).injective
  change PD.PDDeRham.eval p k B Tower n m
    (Affine.PolynomialForms.AffinePolynomialForms.formsEquiv p k B σ r hr hb n
      (e (AdicCompletion.of I P a) ⊗ₜ[W]
        exteriorPower.ιMulti W n (fun i => Finsupp.single (v i) 1))) = _
  rw [Affine.PolynomialForms.AffinePolynomialForms.formsEquiv_eval]
  change Affine.PolynomialFrameTower.AffinePolynomialFrameTower.tensorFormsEquiv p k B σ r hr hb m n
    (PD.InverseLimit.PDInverseLimit.eval p k B Tower m (e (AdicCompletion.of I P a)) ⊗ₜ[W]
      exteriorPower.ιMulti W n (fun i => Finsupp.single (v i) 1)) = _
  rw [FrameCompletion.WittPolynomialFrameCompletion.eval_completedEquiv_of]
  exact PD.FormsTensor.PDFormsTensor.formsEquiv_word W _ σ _ _ _
    (Affine.PolynomialFrameForms.AffinePolynomialFrameForms.basis p k B σ r hr hb m)
    (Affine.PolynomialFrameForms.AffinePolynomialFrameForms.basis_apply p k B σ r hr hb m) n (q m a) v

end

end OAI.AlgebraicGeometry.Crystalline.Cohomology.WittPolynomial.Symbols.WittPolynomialSymbols

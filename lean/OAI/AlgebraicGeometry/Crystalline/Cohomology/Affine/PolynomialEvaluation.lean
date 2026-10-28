import OAI.AlgebraicGeometry.Crystalline.Cohomology.Affine.PolynomialComparison

/-! # Polynomial Evaluation -/

namespace OAI.AlgebraicGeometry.Crystalline.Cohomology.Affine.PolynomialEvaluation.AffinePolynomialEvaluation

noncomputable section

/-! # Evaluation of the original completed comparison is independent of its chosen order -/

universe u

variable (p : ℕ) [Fact p.Prime] (k B σ : Type u) [Field k] [CharP k p]
  [CommRing B] [Algebra k B]
  (r : MvPolynomial σ (WittVector p k) →+* B) (hr : Function.Surjective r)
  (hbase : r.comp (algebraMap (WittVector p k) (MvPolynomial σ (WittVector p k))) =
    (algebraMap k B).comp WittVector.constantCoeff) [Fintype σ]

local notation "W" => WittVector p k
local notation "Poly" => MvPolynomial σ W
local notation "T" => OAI.AlgebraicGeometry.Crystalline.Cohomology.Affine.EnvelopeFrames.AffineEnvelopeFrames.frame p k B Poly r hr hbase
local notation "Tower" => OAI.AlgebraicGeometry.Crystalline.Cohomology.Affine.EnvelopeFrames.AffineEnvelopeFrames.tower p k B Poly r hr hbase
local notation "Completed" => OAI.AlgebraicGeometry.Crystalline.Cohomology.PD.InverseLimit.PDInverseLimit.Ring p k B Tower

theorem component (j n : ℕ) (x : Koszul.Tensor.KoszulTensor.Term W σ Completed j) :
    PD.PDDeRham.eval p k B Tower j n
      ((PolynomialComparison.AffinePolynomialComparison.complexIso p k B σ r hr hbase).hom.f j x) =
    PD.FormsTensor.PDFormsTensor.toForms W (T n).ring σ (RingHom.ker (T n).reduction) (T n).dividedPowers
      (fun i => EnvelopeFrameUniversal.AffineEnvelopeFrameUniversal.coefficient p k B Poly r hr hbase n (MvPolynomial.X i)) j
      (TensorProduct.map (PD.InverseLimit.PDInverseLimit.eval p k B Tower n).toLinearMap LinearMap.id x) := by
  let : LinearOrder σ := LinearOrder.lift' (Fintype.equivFin σ) (Fintype.equivFin σ).injective
  exact PolynomialForms.AffinePolynomialForms.formsEquiv_eval p k B σ r hr hbase j n x

end

end OAI.AlgebraicGeometry.Crystalline.Cohomology.Affine.PolynomialEvaluation.AffinePolynomialEvaluation

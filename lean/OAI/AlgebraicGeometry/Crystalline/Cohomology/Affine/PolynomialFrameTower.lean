import OAI.AlgebraicGeometry.Crystalline.Cohomology.Affine.PolynomialFrameForms
import OAI.AlgebraicGeometry.Crystalline.Cohomology.PD.FormsTensorNaturality
import OAI.AlgebraicGeometry.Crystalline.Cohomology.PD.PDDeRham

/-! # Polynomial Frame Tower -/

namespace OAI.AlgebraicGeometry.Crystalline.Cohomology.Affine.PolynomialFrameTower.AffinePolynomialFrameTower

noncomputable section

/-! # Coordinate forms and derivatives respect the original frame tower -/

open _root_.CategoryTheory

universe u

variable (p : ℕ) [Fact p.Prime] (k B σ : Type u) [Field k] [CharP k p]
  [CommRing B] [Algebra k B]
  (r : MvPolynomial σ (WittVector p k) →+* B) (hr : Function.Surjective r)
  (hbase : r.comp (algebraMap (WittVector p k) (MvPolynomial σ (WittVector p k))) =
    (algebraMap k B).comp WittVector.constantCoeff)

local notation "W" => WittVector p k
local notation "Poly" => MvPolynomial σ W
local notation "T" => OAI.AlgebraicGeometry.Crystalline.Cohomology.Affine.EnvelopeFrames.AffineEnvelopeFrames.frame p k B Poly r hr hbase
local notation "Tower" => OAI.AlgebraicGeometry.Crystalline.Cohomology.Affine.EnvelopeFrames.AffineEnvelopeFrames.tower p k B Poly r hr hbase
local notation "q" => OAI.AlgebraicGeometry.Crystalline.Cohomology.Affine.PolynomialFrameDerivatives.AffinePolynomialFrameDerivatives.quotient p k B σ r hr hbase
local notation "D" => OAI.AlgebraicGeometry.Crystalline.Cohomology.Affine.PolynomialFrameDerivatives.AffinePolynomialFrameDerivatives.derivation p k B σ r hr hbase
local notation "x" => fun n i => OAI.AlgebraicGeometry.Crystalline.Cohomology.Affine.EnvelopeFrameUniversal.AffineEnvelopeFrameUniversal.coefficient p k B Poly r hr hbase n (MvPolynomial.X i)

abbrev Ring (n : ℕ) : Type u := (T n).ring

def transition (n m : ℕ) (h : n ≤ m) : (T m).ring →ₐ[W] (T n).ring :=
  (PD.InverseLimit.PDInverseLimit.transition p k B Tower n m h).hom

theorem transition_quotient (n m : ℕ) (h : n ≤ m)
    (a : PD.EnvelopeDp.PDEnvelope.Envelope W Poly (Ideal.span {(p : W)})
      (Witt.DividedPowers.WittDividedPowers.wittDividedPowers p k) (RingHom.ker r)) :
    transition p k B σ r hr hbase n m h (q m a) = q n a := rfl

theorem derivative_transition (n m : ℕ) (h : n ≤ m) (i : σ) (a : (T m).ring) :
    D n i (transition p k B σ r hr hbase n m h a) =
      transition p k B σ r hr hbase n m h (D m i a) := by
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective a
  change D n i (transition p k B σ r hr hbase n m h (q m a)) =
    transition p k B σ r hr hbase n m h (D m i (q m a))
  rw [transition_quotient, PolynomialFrameDerivatives.AffinePolynomialFrameDerivatives.derivation_quotient,
    PolynomialFrameDerivatives.AffinePolynomialFrameDerivatives.derivation_quotient, transition_quotient]

variable [Fintype σ] [LinearOrder σ]

abbrev Form (n j : ℕ) :=
  PD.DeRham.PDDeRham.Form W (T n).ring (RingHom.ker (T n).reduction) (T n).dividedPowers j

def tensorFormsEquiv (n j : ℕ) : Koszul.Tensor.KoszulTensor.Term W σ (T n).ring j ≃ₗ[(T n).ring]
    Form p k B σ r hr hbase n j :=
  PD.FormsTensor.PDFormsTensor.formsEquiv W (T n).ring σ (RingHom.ker (T n).reduction) (T n).dividedPowers (x n)
    (PolynomialFrameForms.AffinePolynomialFrameForms.basis p k B σ r hr hbase n)
    (PolynomialFrameForms.AffinePolynomialFrameForms.basis_apply p k B σ r hr hbase n) j

theorem tensorFormsEquiv_naturality (n m : ℕ) (h : n ≤ m) (j : ℕ)
    (z : Koszul.Tensor.KoszulTensor.Term W σ (T m).ring j) :
    tensorFormsEquiv p k B σ r hr hbase n j
      (TensorProduct.map (transition p k B σ r hr hbase n m h).toLinearMap LinearMap.id z) =
        PD.PDDeRham.transition p k B Tower j n m h
          (tensorFormsEquiv p k B σ r hr hbase m j z) :=
  PD.FormsTensorNaturality.PDFormsTensorNaturality.formsEquiv_naturality W (T m).ring (T n).ring σ
    (RingHom.ker (T m).reduction) (RingHom.ker (T n).reduction)
    (T m).dividedPowers (T n).dividedPowers (x m) (x n)
    (transition p k B σ r hr hbase n m h)
    (PD.InverseLimit.PDInverseLimit.transition p k B Tower n m h).dp_comp (fun _ => rfl)
    (PolynomialFrameForms.AffinePolynomialFrameForms.basis p k B σ r hr hbase m)
    (PolynomialFrameForms.AffinePolynomialFrameForms.basis_apply p k B σ r hr hbase m)
    (PolynomialFrameForms.AffinePolynomialFrameForms.basis p k B σ r hr hbase n)
    (PolynomialFrameForms.AffinePolynomialFrameForms.basis_apply p k B σ r hr hbase n) j z

end

end OAI.AlgebraicGeometry.Crystalline.Cohomology.Affine.PolynomialFrameTower.AffinePolynomialFrameTower

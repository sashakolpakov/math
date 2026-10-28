import OAI.AlgebraicGeometry.Crystalline.Cohomology.Affine.PolynomialForms
import OAI.AlgebraicGeometry.Crystalline.Cohomology.Koszul.TensorMap

/-! # Polynomial Comparison -/

namespace OAI.AlgebraicGeometry.Crystalline.Cohomology.Affine.PolynomialComparison.AffinePolynomialComparison

noncomputable section

/-!
# The coordinate complex computes the original completed PD differential

Evaluation at each original frame level identifies the coordinate tensor
differential with the actual PD differential. The compatible-form
isomorphisms therefore assemble to an isomorphism of completed complexes.
-/

open _root_.CategoryTheory

universe u

variable (p : ℕ) [Fact p.Prime] (k B σ : Type u) [Field k] [CharP k p]
  [CommRing B] [Algebra k B]
  (r : MvPolynomial σ (WittVector p k) →+* B) (hr : Function.Surjective r)
  (hbase : r.comp (algebraMap (WittVector p k) (MvPolynomial σ (WittVector p k))) =
    (algebraMap k B).comp WittVector.constantCoeff) [Fintype σ]

local notation "W" => WittVector p k
local notation "Poly" => MvPolynomial σ W
local notation "T" => OAI.AlgebraicGeometry.Crystalline.Cohomology.Affine.EnvelopeFrames.AffineEnvelopeFrames.frame p k B Poly r hr hbase
local notation "Q" => OAI.AlgebraicGeometry.Crystalline.Cohomology.Affine.PolynomialFrameTower.AffinePolynomialFrameTower.Ring p k B σ r hr hbase
local notation "Tower" => OAI.AlgebraicGeometry.Crystalline.Cohomology.Affine.EnvelopeFrames.AffineEnvelopeFrames.tower p k B Poly r hr hbase
local notation "C" => OAI.AlgebraicGeometry.Crystalline.Cohomology.PD.InverseLimit.PDInverseLimit.Ring p k B Tower
local notation "D" => OAI.AlgebraicGeometry.Crystalline.Cohomology.Affine.PolynomialOperators.AffinePolynomialOperators.derivative p k B σ r hr hbase
local notation "F" => OAI.AlgebraicGeometry.Crystalline.Cohomology.PD.PDDeRham.complex p k B Tower
local notation "K" => OAI.AlgebraicGeometry.Crystalline.Cohomology.Affine.PolynomialOperators.AffinePolynomialOperators.complex p k B σ r hr hbase

def levelDerivatives (n : ℕ) (i : σ) : Module.End W (Q n) :=
  (PolynomialFrameDerivatives.AffinePolynomialFrameDerivatives.derivation p k B σ r hr hbase n i).toLinearMap

variable [LinearOrder σ]

theorem differential_compatibility (j : ℕ) :
    (PolynomialForms.AffinePolynomialForms.formsEquiv p k B σ r hr hbase (j + 1)).toLinearMap.comp
      (Koszul.Tensor.KoszulTensor.differential W σ C D j) =
        (PD.PDDeRham.differential p k B Tower j).comp
          (PolynomialForms.AffinePolynomialForms.formsEquiv p k B σ r hr hbase j).toLinearMap := by
  apply LinearMap.ext
  intro z
  apply PD.PDDeRham.ext p k B Tower
  intro n
  change PD.PDDeRham.eval p k B Tower (j + 1) n
    (PolynomialForms.AffinePolynomialForms.formsEquiv p k B σ r hr hbase (j + 1) (Koszul.Tensor.KoszulTensor.differential W σ C D j z)) =
      PD.PDDeRham.eval p k B Tower (j + 1) n
        (PD.PDDeRham.differential p k B Tower j (PolynomialForms.AffinePolynomialForms.formsEquiv p k B σ r hr hbase j z))
  rw [PolynomialForms.AffinePolynomialForms.formsEquiv_eval, PD.PDDeRham.eval_differential,
    PolynomialForms.AffinePolynomialForms.formsEquiv_eval]
  have he := LinearMap.congr_fun (Koszul.TensorMap.KoszulTensorMap.differential_naturality W σ C (Q n) D
    (levelDerivatives p k B σ r hr hbase n) (PD.InverseLimit.PDInverseLimit.eval p k B Tower n).toLinearMap (fun _ _ => rfl) j) z
  change TensorProduct.map (PD.InverseLimit.PDInverseLimit.eval p k B Tower n).toLinearMap LinearMap.id
    (Koszul.Tensor.KoszulTensor.differential W σ C D j z) =
      Koszul.Tensor.KoszulTensor.differential W σ (Q n) (levelDerivatives p k B σ r hr hbase n) j
        (TensorProduct.map (PD.InverseLimit.PDInverseLimit.eval p k B Tower n).toLinearMap LinearMap.id z) at he
  rw [he]
  exact LinearMap.congr_fun (PD.DeRhamTensor.PDDeRhamTensor.differential_compatibility W (Q n) σ
    (RingHom.ker (T n).reduction)
    (T n).dividedPowers (fun i => EnvelopeFrameUniversal.AffineEnvelopeFrameUniversal.coefficient p k B Poly r hr hbase n (MvPolynomial.X i))
    (levelDerivatives p k B σ r hr hbase n) (PolynomialFrameForms.AffinePolynomialFrameForms.D_eq_sum p k B σ r hr hbase n) j)
      (TensorProduct.map (PD.InverseLimit.PDInverseLimit.eval p k B Tower n).toLinearMap LinearMap.id z)

def componentIso (j : ℕ) : (K).X j ≅ (F).X j where
  hom := ModuleCat.ofHom (PolynomialForms.AffinePolynomialForms.formsEquiv p k B σ r hr hbase j).toLinearMap
  inv := ModuleCat.ofHom (PolynomialForms.AffinePolynomialForms.formsEquiv p k B σ r hr hbase j).symm.toLinearMap
  hom_inv_id := ModuleCat.hom_ext (LinearMap.ext (fun x =>
    (PolynomialForms.AffinePolynomialForms.formsEquiv p k B σ r hr hbase j).symm_apply_apply x))
  inv_hom_id := ModuleCat.hom_ext (LinearMap.ext (fun x =>
    (PolynomialForms.AffinePolynomialForms.formsEquiv p k B σ r hr hbase j).apply_symm_apply x))

def orderedComplexIso : K ≅ F :=
  HomologicalComplex.Hom.isoOfComponents
    (componentIso p k B σ r hr hbase)
    (by
      intro j l hjl
      have hl : j + 1 = l := hjl
      subst l
      dsimp only [PolynomialOperators.AffinePolynomialOperators.complex, Koszul.Tensor.KoszulTensor.complex, PD.PDDeRham.complex]
      rw [CochainComplex.of_d, CochainComplex.of_d]
      apply ModuleCat.hom_ext
      exact (differential_compatibility p k B σ r hr hbase j).symm)

omit [LinearOrder σ] in
def complexIso : K ≅ F := by
  letI : LinearOrder σ := LinearOrder.lift' (Fintype.equivFin σ) (Fintype.equivFin σ).injective
  exact orderedComplexIso p k B σ r hr hbase

end

end OAI.AlgebraicGeometry.Crystalline.Cohomology.Affine.PolynomialComparison.AffinePolynomialComparison

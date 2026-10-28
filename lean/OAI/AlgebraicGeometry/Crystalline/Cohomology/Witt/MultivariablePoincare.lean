import OAI.AlgebraicGeometry.Crystalline.Cohomology.Witt.WittMultivariableForms
import OAI.AlgebraicGeometry.Crystalline.Cohomology.Witt.MultivariableTensor
import OAI.AlgebraicGeometry.Crystalline.Cohomology.Koszul.TensorMap

/-! # Multivariable Poincare -/

namespace OAI.AlgebraicGeometry.Crystalline.Cohomology.Witt.MultivariablePoincare.WittMultivariablePoincare

noncomputable section

/-!
# Poincaré homotopy for the actual completed multivariable crystalline forms

Evaluation identifies the tensor differential with the coordinatewise
actual PD differential. The completed form comparison is therefore a
complex isomorphism, and the integral contraction transfers to the
actual inverse-limit PD de Rham complex with constants W(k).
-/

open _root_.CategoryTheory

universe u

variable (p : ℕ) [Fact p.Prime] (k σ : Type u) [Field k] [CharP k p] [PerfectRing k p] [Fintype σ]

local notation "W" => WittVector p k
local notation "Q" => OAI.AlgebraicGeometry.Crystalline.Cohomology.Witt.MultivariableThickening.WittMultivariableThickening.Ring p k σ
local notation "T" => OAI.AlgebraicGeometry.Crystalline.Cohomology.Witt.MultivariableTower.WittMultivariableTower.tower p k σ
local notation "C" => OAI.AlgebraicGeometry.Crystalline.Cohomology.PD.InverseLimit.PDInverseLimit.Ring p k k T
local notation "D" => OAI.AlgebraicGeometry.Crystalline.Cohomology.Witt.MultivariableOperators.WittMultivariableOperators.derivative p k σ
local notation "F" => OAI.AlgebraicGeometry.Crystalline.Cohomology.PD.PDDeRham.complex p k k T
local notation "K" => OAI.AlgebraicGeometry.Crystalline.Cohomology.Witt.MultivariableTensor.WittMultivariableTensor.complex p k σ

def levelDerivatives (n : ℕ) (i : σ) : Module.End W (Q n) :=
  (MultivariableForms.WittMultivariableForms.derivation p k σ n i).toLinearMap

variable [LinearOrder σ]

theorem differential_compatibility (j : ℕ) :
    (WittMultivariableForms.formsEquiv p k σ (j + 1)).toLinearMap.comp
      (Koszul.Tensor.KoszulTensor.differential W σ C D j) =
        (PD.PDDeRham.differential p k k T j).comp
          (WittMultivariableForms.formsEquiv p k σ j).toLinearMap := by
  apply LinearMap.ext
  intro z
  apply PD.PDDeRham.ext p k k T
  intro n
  change PD.PDDeRham.eval p k k T (j + 1) n
    (WittMultivariableForms.formsEquiv p k σ (j + 1) (Koszul.Tensor.KoszulTensor.differential W σ C D j z)) =
      PD.PDDeRham.eval p k k T (j + 1) n
        (PD.PDDeRham.differential p k k T j (WittMultivariableForms.formsEquiv p k σ j z))
  rw [WittMultivariableForms.formsEquiv_eval, PD.PDDeRham.eval_differential,
    WittMultivariableForms.formsEquiv_eval]
  have he := LinearMap.congr_fun (Koszul.TensorMap.KoszulTensorMap.differential_naturality W σ C (Q n) D
    (levelDerivatives p k σ n) (PD.InverseLimit.PDInverseLimit.eval p k k T n).toLinearMap (fun _ _ => rfl) j) z
  change TensorProduct.map (PD.InverseLimit.PDInverseLimit.eval p k k T n).toLinearMap LinearMap.id
    (Koszul.Tensor.KoszulTensor.differential W σ C D j z) =
      Koszul.Tensor.KoszulTensor.differential W σ (Q n) (levelDerivatives p k σ n) j
        (TensorProduct.map (PD.InverseLimit.PDInverseLimit.eval p k k T n).toLinearMap LinearMap.id z) at he
  rw [he]
  exact LinearMap.congr_fun (PD.DeRhamTensor.PDDeRhamTensor.differential_compatibility W (Q n) σ
    (RingHom.ker (MultivariableThickening.WittMultivariableThickening.reduction p k σ n))
    (MultivariableThickening.WittMultivariableThickening.kernelDividedPowers p k σ n) (MultivariableForms.WittMultivariableForms.coordinate p k σ n)
    (levelDerivatives p k σ n) (MultivariableForms.WittMultivariableForms.D_eq_sum p k σ n) j)
      (TensorProduct.map (PD.InverseLimit.PDInverseLimit.eval p k k T n).toLinearMap LinearMap.id z)

def componentIso (j : ℕ) : (K).X j ≅ (F).X j where
  hom := ModuleCat.ofHom (WittMultivariableForms.formsEquiv p k σ j).toLinearMap
  inv := ModuleCat.ofHom (WittMultivariableForms.formsEquiv p k σ j).symm.toLinearMap
  hom_inv_id := ModuleCat.hom_ext (LinearMap.ext (fun x =>
    (WittMultivariableForms.formsEquiv p k σ j).symm_apply_apply x))
  inv_hom_id := ModuleCat.hom_ext (LinearMap.ext (fun x =>
    (WittMultivariableForms.formsEquiv p k σ j).apply_symm_apply x))

def orderedComplexIso : K ≅ F :=
  HomologicalComplex.Hom.isoOfComponents
    (componentIso p k σ)
    (by
      intro j l hjl
      have hl : j + 1 = l := hjl
      subst l
      dsimp only [MultivariableTensor.WittMultivariableTensor.complex, Koszul.Tensor.KoszulTensor.complex, PD.PDDeRham.complex]
      rw [CochainComplex.of_d, CochainComplex.of_d]
      apply ModuleCat.hom_ext
      exact (differential_compatibility p k σ j).symm)

omit [LinearOrder σ] in
def complexIso : K ≅ F := by
  letI : LinearOrder σ := LinearOrder.lift' (Fintype.equivFin σ) (Fintype.equivFin σ).injective
  exact orderedComplexIso p k σ

omit [LinearOrder σ] in
/-- The actual inverse-limit multivariable crystalline form complex contracts onto W(k). -/
def homotopyEquiv : HomotopyEquiv
    ((CochainComplex.single₀ (ModuleCat W)).obj (ModuleCat.of W W)) F :=
  (MultivariableTensor.WittMultivariableTensor.homotopyEquiv p k σ).trans (HomotopyEquiv.ofIso (complexIso p k σ))

omit [LinearOrder σ] in
def augmentation : (CochainComplex.single₀ (ModuleCat W)).obj (ModuleCat.of W W) ⟶ F :=
  (homotopyEquiv p k σ).hom

omit [LinearOrder σ] in
instance augmentation_quasiIso : QuasiIso (augmentation p k σ) :=
  HomotopyEquiv.quasiIso_hom (homotopyEquiv p k σ)

omit [LinearOrder σ] in
def degreeZeroHomologyIso : (F).homology 0 ≅ ModuleCat.of W W :=
  ((homotopyEquiv p k σ).toHomologyIso 0).symm ≪≫
    HomologicalComplex.singleObjHomologySelfIso (ComplexShape.up ℕ) 0 (ModuleCat.of W W)

end

end OAI.AlgebraicGeometry.Crystalline.Cohomology.Witt.MultivariablePoincare.WittMultivariablePoincare

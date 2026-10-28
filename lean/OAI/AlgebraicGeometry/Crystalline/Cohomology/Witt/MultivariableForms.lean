import OAI.AlgebraicGeometry.Crystalline.Cohomology.Witt.MultivariableTower

/-! # Multivariable Forms -/

namespace OAI.AlgebraicGeometry.Crystalline.Cohomology.Witt.MultivariableForms.WittMultivariableForms

noncomputable section

/-!
# Coordinate forms on the actual multivariable crystalline tower

Identifying the explicit quotient ideal with the reduction kernel
preserves the coefficient-linear form equivalence. Coordinate bases and
their tensor descriptions therefore apply to the actual crystalline forms.
-/

open _root_.CategoryTheory

universe u

variable (p : ℕ) [Fact p.Prime] (k σ : Type u) [Field k] [CharP k p] [PerfectRing k p]

local notation "W" => WittVector p k
local notation "K" => FractionRing W
local notation "I" => Ideal.span {(p : W)}
local notation "δ" => OAI.AlgebraicGeometry.Crystalline.Cohomology.Witt.DividedPowers.WittDividedPowers.wittDividedPowers p k
local notation "h" => IsFractionRing.injective W K
local notation "unit" => OAI.AlgebraicGeometry.Crystalline.Cohomology.WittPolynomial.Thickening.WittPolynomialThickening.base_unit p k
local notation "Q" => OAI.AlgebraicGeometry.Crystalline.Cohomology.Witt.MultivariableThickening.WittMultivariableThickening.Ring p k σ
local notation "L" => OAI.AlgebraicGeometry.Crystalline.Cohomology.WittPolynomial.Thickening.WittPolynomialThickening.baseIdeal p k
local notation "subDP" => OAI.AlgebraicGeometry.Crystalline.Cohomology.WittPolynomial.Thickening.WittPolynomialThickening.baseIdeal_subDP p k

def quotientIdeal (n : ℕ) : Ideal (Q n) := QuotientMultivariableD.QuotientMultivariableForms.ideal W σ I (L n)

def quotientPowers (n : ℕ) : DividedPowers (quotientIdeal p k σ n) :=
  QuotientMultivariableD.QuotientMultivariableForms.dividedPowers W σ K h I δ unit (L n) (subDP n)

local notation "J" => OAI.AlgebraicGeometry.Crystalline.Cohomology.Witt.MultivariableForms.WittMultivariableForms.quotientIdeal p k σ
local notation "ε" => OAI.AlgebraicGeometry.Crystalline.Cohomology.Witt.MultivariableForms.WittMultivariableForms.quotientPowers p k σ
local notation "Jk" => fun n => RingHom.ker (OAI.AlgebraicGeometry.Crystalline.Cohomology.Witt.MultivariableThickening.WittMultivariableThickening.reduction p k σ n)
local notation "εk" => OAI.AlgebraicGeometry.Crystalline.Cohomology.Witt.MultivariableThickening.WittMultivariableThickening.kernelDividedPowers p k σ

abbrev Form (n j : ℕ) := PD.DeRham.PDDeRham.Form W (Q n) (Jk n) (εk n) j

theorem identity_toKernel (n : ℕ) :
    DividedPowers.IsDPMorphism (ε n) (εk n) (RingHom.id (Q n)) where
  ideal_comp := by
    change (J n).map (RingHom.id (Q n)) ≤ Jk n
    rw [Ideal.map_id]
    exact (MultivariableThickening.WittMultivariableThickening.reduction_kernel p k σ n).symm.le
  dpow_comp _ _ := rfl

theorem identity_fromKernel (n : ℕ) :
    DividedPowers.IsDPMorphism (εk n) (ε n) (RingHom.id (Q n)) where
  ideal_comp := by
    change (Jk n).map (RingHom.id (Q n)) ≤ J n
    rw [Ideal.map_id]
    exact (MultivariableThickening.WittMultivariableThickening.reduction_kernel p k σ n).le
  dpow_comp _ _ := rfl

def formsEquiv (n j : ℕ) : PD.DeRham.PDDeRham.Form W (Q n) (J n) (ε n) j ≃ₗ[W] Form p k σ n j :=
  PD.DeRhamEquivalence.PDDeRhamEquivalence.formsEquiv (A := CommAlgCat.of W (Q n)) (B := CommAlgCat.of W (Q n))
    AlgEquiv.refl (identity_toKernel p k σ n) (identity_fromKernel p k σ n) j

def formsLinearEquiv (n j : ℕ) : PD.DeRham.PDDeRham.Form W (Q n) (J n) (ε n) j ≃ₗ[Q n] Form p k σ n j where
  __ := (formsEquiv p k σ n j).toAddEquiv
  map_smul' a ω := PD.DeRhamGlobal.PDDeRhamGlobal.formMap_smul
    (A := CommAlgCat.of W (Q n)) (B := CommAlgCat.of W (Q n))
    (CommAlgCat.ofHom (AlgHom.id W (Q n))) (identity_toKernel p k σ n) j a ω

theorem formsLinearEquiv_D (n : ℕ) (a : Q n) :
    formsLinearEquiv p k σ n 1 (PD.OneForms.PDOneForms.D W (Q n) (J n) (ε n) a) =
      PD.OneForms.PDOneForms.D W (Q n) (Jk n) (εk n) a :=
  PD.DeRhamEquivalence.PDDeRhamEquivalence.formsEquiv_D (A := CommAlgCat.of W (Q n)) (B := CommAlgCat.of W (Q n))
    AlgEquiv.refl (identity_toKernel p k σ n) (identity_fromKernel p k σ n) a

def coordinate (n : ℕ) : σ → Q n := QuotientMultivariableD.QuotientMultivariableForms.coordinate W σ (L n)

def derivation (n : ℕ) (i : σ) : Derivation W (Q n) (Q n) :=
  QuotientMultivariableD.QuotientMultivariableForms.derivation W σ K h I δ unit (L n) i

variable [Fintype σ]

def basis (n : ℕ) : Module.Basis σ (Q n) (Form p k σ n 1) :=
  (QuotientMultivariableD.QuotientMultivariableForms.basis W σ K h I δ unit (L n) (subDP n)).map (formsLinearEquiv p k σ n 1)

theorem basis_apply (n : ℕ) (i : σ) :
    basis p k σ n i = PD.OneForms.PDOneForms.D W (Q n) (Jk n) (εk n) (coordinate p k σ n i) := by
  let bq : Module.Basis σ (Q n) (PD.DeRham.PDDeRham.Form W (Q n) (J n) (ε n) 1) :=
    QuotientMultivariableD.QuotientMultivariableForms.basis W σ K h I δ unit (L n) (subDP n)
  change (bq.map (formsLinearEquiv p k σ n 1)) i = _
  rw [Module.Basis.map_apply]
  exact (congrArg (formsLinearEquiv p k σ n 1)
    (QuotientMultivariableD.QuotientMultivariableForms.basis_apply W σ K h I δ unit (L n) (subDP n) i)).trans
      (formsLinearEquiv_D p k σ n (coordinate p k σ n i))

theorem D_eq_sum (n : ℕ) (a : Q n) :
    PD.OneForms.PDOneForms.D W (Q n) (Jk n) (εk n) a =
      ∑ i, derivation p k σ n i a • PD.OneForms.PDOneForms.D W (Q n) (Jk n) (εk n) (coordinate p k σ n i) := by
  have hs := congrArg (formsLinearEquiv p k σ n 1)
    (QuotientMultivariableD.QuotientMultivariableForms.D_eq_sum W σ K h I δ unit (L n) (subDP n) a)
  change formsLinearEquiv p k σ n 1 (PD.OneForms.PDOneForms.D W (Q n) (J n) (ε n) a) =
    formsLinearEquiv p k σ n 1 (∑ i, derivation p k σ n i a •
      PD.OneForms.PDOneForms.D W (Q n) (J n) (ε n) (coordinate p k σ n i)) at hs
  simpa only [map_sum, map_smul, formsLinearEquiv_D] using hs

variable [LinearOrder σ]

def tensorFormsEquiv (n j : ℕ) : Koszul.Tensor.KoszulTensor.Term W σ (Q n) j ≃ₗ[Q n] Form p k σ n j :=
  PD.FormsTensor.PDFormsTensor.formsEquiv W (Q n) σ (Jk n) (εk n) (coordinate p k σ n)
    (basis p k σ n) (basis_apply p k σ n) j

def formMap (n m : ℕ) (hnm : n ≤ m) (j : ℕ) : Form p k σ m j →ₗ[W] Form p k σ n j :=
  PD.DeRhamGlobal.PDDeRhamGlobal.formMap (CommAlgCat.ofHom (MultivariableTower.WittMultivariableTower.transitionHom p k σ n m hnm))
    (MultivariableTower.WittMultivariableTower.transitionHom_isDPMorphism p k σ n m hnm) j

theorem tensorFormsEquiv_naturality (n m : ℕ) (hnm : n ≤ m) (j : ℕ) (z : Koszul.Tensor.KoszulTensor.Term W σ (Q m) j) :
    tensorFormsEquiv p k σ n j
      (TensorProduct.map (MultivariableTower.WittMultivariableTower.transitionHom p k σ n m hnm).toLinearMap LinearMap.id z) =
        formMap p k σ n m hnm j (tensorFormsEquiv p k σ m j z) :=
  PD.FormsTensorNaturality.PDFormsTensorNaturality.formsEquiv_naturality W (Q m) (Q n) σ (Jk m) (Jk n) (εk m) (εk n)
    (coordinate p k σ m) (coordinate p k σ n) (MultivariableTower.WittMultivariableTower.transitionHom p k σ n m hnm)
    (MultivariableTower.WittMultivariableTower.transitionHom_isDPMorphism p k σ n m hnm) (fun _ => rfl)
    (basis p k σ m) (basis_apply p k σ m) (basis p k σ n) (basis_apply p k σ n) j z

end

end OAI.AlgebraicGeometry.Crystalline.Cohomology.Witt.MultivariableForms.WittMultivariableForms

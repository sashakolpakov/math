import OAI.AlgebraicGeometry.Crystalline.Cohomology.Finite.TensorInverseLimit
import OAI.AlgebraicGeometry.Crystalline.Cohomology.Affine.PolynomialOperators

/-! # Polynomial Forms -/

namespace OAI.AlgebraicGeometry.Crystalline.Cohomology.Affine.PolynomialForms.AffinePolynomialForms

noncomputable section

/-!
# Completed forms on the original affine polynomial frame

Finite free tensor products commute with the inverse limit. The proved
coordinate equivalences on the original frame levels therefore identify
all compatible PD forms with exterior forms of compatible coefficients.
-/

open Classical
open scoped TensorProduct

universe u

variable (p : ℕ) [Fact p.Prime] (k B σ : Type u) [Field k] [CharP k p]
  [CommRing B] [Algebra k B]
  (r : MvPolynomial σ (WittVector p k) →+* B) (hr : Function.Surjective r)
  (hbase : r.comp (algebraMap (WittVector p k) (MvPolynomial σ (WittVector p k))) =
    (algebraMap k B).comp WittVector.constantCoeff)

local notation "W" => WittVector p k
local notation "Poly" => MvPolynomial σ W
local notation "T" => OAI.AlgebraicGeometry.Crystalline.Cohomology.Affine.EnvelopeFrames.AffineEnvelopeFrames.frame p k B Poly r hr hbase
local notation "Q" => OAI.AlgebraicGeometry.Crystalline.Cohomology.Affine.PolynomialFrameTower.AffinePolynomialFrameTower.Ring p k B σ r hr hbase
local notation "Tower" => OAI.AlgebraicGeometry.Crystalline.Cohomology.Affine.EnvelopeFrames.AffineEnvelopeFrames.tower p k B Poly r hr hbase
local notation "C" => OAI.AlgebraicGeometry.Crystalline.Cohomology.PD.InverseLimit.PDInverseLimit.Ring p k B Tower
local notation "Ω" => OAI.AlgebraicGeometry.Crystalline.Cohomology.PD.PDDeRham.CompletedForm p k B Tower

def ringTransition (n m : ℕ) (hnm : n ≤ m) : Q m →ₗ[W] Q n :=
  (PolynomialFrameTower.AffinePolynomialFrameTower.transition p k B σ r hr hbase n m hnm).toLinearMap

def compatibleRingEquiv : Cohomology.Module.InverseLimit.ModuleInverseLimit.compatible W Q (ringTransition p k B σ r hr hbase) ≃ₗ[W] C where
  toFun x := ⟨x.val, fun n m hnm => x.property n m hnm⟩
  invFun x := ⟨x.val, fun n m hnm => x.property n m hnm⟩
  left_inv _ := Subtype.ext rfl
  right_inv _ := Subtype.ext rfl
  map_add' _ _ := Subtype.ext rfl
  map_smul' _ _ := Subtype.ext rfl

local instance formGroupFamily (j : ℕ) : ∀ n, AddCommGroup (PolynomialFrameTower.AffinePolynomialFrameTower.Form p k B σ r hr hbase n j) :=
  fun n => inferInstanceAs (AddCommGroup (PD.DeRham.PDDeRham.Form W (Q n)
    (RingHom.ker (T n).reduction)
    (T n).dividedPowers j))

local instance formModuleFamily (j : ℕ) : ∀ n, Module W (PolynomialFrameTower.AffinePolynomialFrameTower.Form p k B σ r hr hbase n j) :=
  fun n => inferInstanceAs (Module W (PD.DeRham.PDDeRham.Form W (Q n)
    (RingHom.ker (T n).reduction)
    (T n).dividedPowers j))

def formsCompatibleEquiv (j : ℕ) :
    Cohomology.Module.InverseLimit.ModuleInverseLimit.compatible W (fun n => PolynomialFrameTower.AffinePolynomialFrameTower.Form p k B σ r hr hbase n j)
      (fun n m hnm => PD.PDDeRham.transition p k B Tower j n m hnm) ≃ₗ[W] Ω j where
  toFun x := ⟨x.val, fun n m hnm => x.property n m hnm⟩
  invFun x := ⟨x.val, fun n m hnm => x.property n m hnm⟩
  left_inv _ := Subtype.ext rfl
  right_inv _ := Subtype.ext rfl
  map_add' _ _ := Subtype.ext rfl
  map_smul' _ _ := Subtype.ext rfl

variable [Fintype σ] [LinearOrder σ]

local instance indexFintype (j : ℕ) : Fintype (Set.powersetCard σ j) := Fintype.ofFinite _

def exteriorBasis (j : ℕ) : Module.Basis (Set.powersetCard σ j) W (⋀[W]^j (σ →₀ W)) :=
  (Finsupp.basisSingleOne : Module.Basis σ W (σ →₀ W)).exteriorPower j

def tensorLimitEquiv (j : ℕ) : Koszul.Tensor.KoszulTensor.Term W σ C j ≃ₗ[W]
    Cohomology.Module.InverseLimit.ModuleInverseLimit.compatible W (fun n => Koszul.Tensor.KoszulTensor.Term W σ (Q n) j)
      (Finite.TensorInverseLimit.FiniteTensorInverseLimit.tensorTransition W (⋀[W]^j (σ →₀ W)) Q (ringTransition p k B σ r hr hbase)) :=
  (TensorProduct.congr (compatibleRingEquiv p k B σ r hr hbase).symm (LinearEquiv.refl W _)).trans
    (Finite.TensorInverseLimit.FiniteTensorInverseLimit.equiv W (Set.powersetCard σ j) (⋀[W]^j (σ →₀ W)) (exteriorBasis p k σ j)
      Q (ringTransition p k B σ r hr hbase))

def tensorFormsLimitEquiv (j : ℕ) :
    Cohomology.Module.InverseLimit.ModuleInverseLimit.compatible W (fun n => Koszul.Tensor.KoszulTensor.Term W σ (Q n) j)
      (Finite.TensorInverseLimit.FiniteTensorInverseLimit.tensorTransition W (⋀[W]^j (σ →₀ W)) Q (ringTransition p k B σ r hr hbase)) ≃ₗ[W]
        Cohomology.Module.InverseLimit.ModuleInverseLimit.compatible W (fun n => PolynomialFrameTower.AffinePolynomialFrameTower.Form p k B σ r hr hbase n j)
          (fun n m hnm => PD.PDDeRham.transition p k B Tower j n m hnm) :=
  Cohomology.Module.InverseLimit.ModuleInverseLimit.equiv W (fun n => Koszul.Tensor.KoszulTensor.Term W σ (Q n) j)
    (Finite.TensorInverseLimit.FiniteTensorInverseLimit.tensorTransition W (⋀[W]^j (σ →₀ W)) Q (ringTransition p k B σ r hr hbase))
    (fun n => PolynomialFrameTower.AffinePolynomialFrameTower.Form p k B σ r hr hbase n j)
    (fun n m hnm => PD.PDDeRham.transition p k B Tower j n m hnm)
    (fun n => (PolynomialFrameTower.AffinePolynomialFrameTower.tensorFormsEquiv p k B σ r hr hbase n j).restrictScalars W)
    (fun n m hnm z => PolynomialFrameTower.AffinePolynomialFrameTower.tensorFormsEquiv_naturality p k B σ r hr hbase n m hnm j z)

/-- The actual compatible PD forms are the tensor forms of the compatible coefficient ring. -/
def formsEquiv (j : ℕ) : Koszul.Tensor.KoszulTensor.Term W σ C j ≃ₗ[W] Ω j :=
  (tensorLimitEquiv p k B σ r hr hbase j).trans (tensorFormsLimitEquiv p k B σ r hr hbase j) |>.trans (formsCompatibleEquiv p k B σ r hr hbase j)

theorem tensorLimitEquiv_eval (j n : ℕ) (z : Koszul.Tensor.KoszulTensor.Term W σ C j) :
    (tensorLimitEquiv p k B σ r hr hbase j z).val n =
      TensorProduct.map (PD.InverseLimit.PDInverseLimit.eval p k B Tower n).toLinearMap LinearMap.id z := by
  change Cohomology.Module.InverseLimit.ModuleInverseLimit.eval W (fun n => Q n ⊗[W] (⋀[W]^j (σ →₀ W)))
    (Finite.TensorInverseLimit.FiniteTensorInverseLimit.tensorTransition W (⋀[W]^j (σ →₀ W)) Q (ringTransition p k B σ r hr hbase)) n
      (Finite.TensorInverseLimit.FiniteTensorInverseLimit.equiv W (Set.powersetCard σ j) (⋀[W]^j (σ →₀ W)) (exteriorBasis p k σ j)
        Q (ringTransition p k B σ r hr hbase)
          (TensorProduct.congr (compatibleRingEquiv p k B σ r hr hbase).symm (LinearEquiv.refl W _) z)) = _
  rw [Finite.TensorInverseLimit.FiniteTensorInverseLimit.equiv_eval]
  change TensorProduct.map (Cohomology.Module.InverseLimit.ModuleInverseLimit.eval W Q (ringTransition p k B σ r hr hbase) n) LinearMap.id
    (TensorProduct.map (compatibleRingEquiv p k B σ r hr hbase).symm.toLinearMap LinearMap.id z) = _
  rw [TensorProduct.map_map, LinearMap.id_comp]
  rfl

theorem formsEquiv_eval (j n : ℕ) (z : Koszul.Tensor.KoszulTensor.Term W σ C j) :
    PD.PDDeRham.eval p k B Tower j n (formsEquiv p k B σ r hr hbase j z) =
      PolynomialFrameTower.AffinePolynomialFrameTower.tensorFormsEquiv p k B σ r hr hbase n j
        (TensorProduct.map (PD.InverseLimit.PDInverseLimit.eval p k B Tower n).toLinearMap LinearMap.id z) := by
  change PolynomialFrameTower.AffinePolynomialFrameTower.tensorFormsEquiv p k B σ r hr hbase n j ((tensorLimitEquiv p k B σ r hr hbase j z).val n) = _
  rw [tensorLimitEquiv_eval]

end

end OAI.AlgebraicGeometry.Crystalline.Cohomology.Affine.PolynomialForms.AffinePolynomialForms

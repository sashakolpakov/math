import OAI.AlgebraicGeometry.Crystalline.Cohomology.Koszul.SuccessiveHomotopy
import OAI.AlgebraicGeometry.Crystalline.Cohomology.TensorDegree
import OAI.AlgebraicGeometry.Crystalline.Cohomology.SingleRetraction

/-! # Constants Retraction -/

namespace OAI.AlgebraicGeometry.Crystalline.Cohomology.Koszul.ConstantsRetraction.KoszulConstantsRetraction

noncomputable section

/-!
# Tensor contraction onto an explicit constant module

This packages the coordinate calculation when constants form an arbitrary
coefficient module, including a quotient of the base ring.
-/

open _root_.CategoryTheory
open scoped TensorProduct

universe u

variable (R σ M A : Type u) [CommRing R] [Fintype σ]
  [AddCommGroup M] [Module R M] [AddCommGroup A] [Module R A]
  (D S : σ → Module.End R M) (hcomm : ∀ i j, Function.Commute (D i) (D j))
  (hright : ∀ i m, D i (S i m) = m)
  (hcommS : ∀ i j, j ≠ i → ∀ m, D j (S i m) = S i (D j m))
  (l : List σ) (hl : ∀ i, i ∈ l) (c : A →ₗ[R] M) (r : M →ₗ[R] A)
  (hrc : r.comp c = LinearMap.id)
  (hc : ∀ i a, D i (c a) = 0)
  (hprojection : SuccessiveHomotopy.KoszulSuccessiveHomotopy.coefficient R σ M D S l = c.comp r)

local notation "K" => OAI.AlgebraicGeometry.Crystalline.Cohomology.Koszul.Tensor.KoszulTensor.complex R σ M D hcomm
local notation "e₀" => OAI.AlgebraicGeometry.Crystalline.Cohomology.TensorDegree.TensorDegreeZero.equiv R σ M
local notation "q" => OAI.AlgebraicGeometry.Crystalline.Cohomology.Koszul.SuccessiveHomotopy.KoszulSuccessiveHomotopy.chain R σ M D S hcomm l

def inclusionZero : A →ₗ[R] Tensor.KoszulTensor.Term R σ M 0 := (e₀).symm.toLinearMap.comp c

def retractionZero : Tensor.KoszulTensor.Term R σ M 0 →ₗ[R] A := r.comp (e₀).toLinearMap

omit [Fintype σ] in
include hrc in
theorem retraction_inclusion :
    (retractionZero R σ M A r).comp (inclusionZero R σ M A c) = LinearMap.id := by
  apply LinearMap.ext
  intro a
  change r (e₀ ((e₀).symm (c a))) = a
  rw [LinearEquiv.apply_symm_apply]
  exact LinearMap.congr_fun hrc a

include hc in
theorem differential_inclusion :
    (Tensor.KoszulTensor.differential R σ M D 0).comp (inclusionZero R σ M A c) = 0 := by
  apply LinearMap.ext
  intro a
  change Tensor.KoszulTensor.differential R σ M D 0 ((e₀).symm (c a)) = 0
  rw [TensorDegree.TensorDegreeZero.equiv_symm, Tensor.KoszulTensor.differential_tmul]
  apply Finset.sum_eq_zero
  intro i _
  rw [hc, TensorProduct.zero_tmul]

include hright hcommS hprojection in
theorem projection_zero : (q).f 0 =
    ModuleCat.ofHom ((inclusionZero R σ M A c).comp (retractionZero R σ M A r)) := by
  have hf := SuccessiveHomotopy.KoszulSuccessiveHomotopy.chain_f R σ M D S hcomm hright hcommS l 0
  rw [hprojection, ExteriorCoordinate.ExteriorCoordinateProjection.successive_zero] at hf
  apply hf.trans
  apply ModuleCat.hom_ext
  exact (TensorDegree.TensorDegreeZero.conjugate R σ M (c.comp r)).symm

def inclusionHom : ModuleCat.of R A ⟶ (K).X 0 := ModuleCat.ofHom (inclusionZero R σ M A c)

def retractionHom : (K).X 0 ⟶ ModuleCat.of R A := ModuleCat.ofHom (retractionZero R σ M A r)

include hc in
theorem differential_inclusionHom : inclusionHom R σ M A D hcomm c ≫ (K).d 0 1 = 0 := by
  apply ModuleCat.hom_ext
  have hd := CoordinateHomotopy.KoszulCoordinateHomotopy.complex_d R σ M D hcomm 0
  exact (congrArg (fun f : (K).X 0 ⟶ (K).X 1 => f.hom.comp (inclusionZero R σ M A c)) hd).trans
    (differential_inclusion R σ M A D c hc)

include hrc in
theorem retraction_inclusionHom : inclusionHom R σ M A D hcomm c ≫ retractionHom R σ M A D hcomm r =
    𝟙 (ModuleCat.of R A) := ModuleCat.hom_ext (retraction_inclusion R σ M A c r hrc)

include hright hcommS hprojection in
theorem inclusion_retractionHom : retractionHom R σ M A D hcomm r ≫ inclusionHom R σ M A D hcomm c =
    (q).f 0 := (projection_zero R σ M A D S hcomm hright hcommS l c r hprojection).symm

def homotopyEquiv : HomotopyEquiv ((CochainComplex.single₀ (ModuleCat R)).obj (ModuleCat.of R A)) K :=
  SingleRetraction.SingleRetractionHomotopy.homotopyEquiv K (ModuleCat.of R A) q
    (SuccessiveHomotopy.KoszulSuccessiveHomotopy.homotopy R σ M D S hcomm l)
    (inclusionHom R σ M A D hcomm c) (retractionHom R σ M A D hcomm r)
    (differential_inclusionHom R σ M A D hcomm c hc) (retraction_inclusionHom R σ M A D hcomm c r hrc)
    (inclusion_retractionHom R σ M A D S hcomm hright hcommS l c r hprojection)
    (SuccessiveHomotopy.KoszulSuccessiveHomotopy.chain_positive R σ M D S hcomm hright hcommS l hl)

end

end OAI.AlgebraicGeometry.Crystalline.Cohomology.Koszul.ConstantsRetraction.KoszulConstantsRetraction

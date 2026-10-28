import OAI.AlgebraicGeometry.Crystalline.Cohomology.Koszul.SuccessiveHomotopy
import OAI.AlgebraicGeometry.Crystalline.Cohomology.FreeDivided.Constants
import OAI.AlgebraicGeometry.Crystalline.Cohomology.TensorDegree
import OAI.AlgebraicGeometry.Crystalline.Cohomology.SingleRetraction
import Mathlib.Algebra.Homology.QuasiIso

/-! # Koszul Homotopy -/

namespace OAI.AlgebraicGeometry.Crystalline.Cohomology.FreeDivided.KoszulHomotopy.FreeDividedKoszulHomotopy

noncomputable section

/-!
# A multivariable divided-polynomial tensor contraction

The commuting actual coordinate derivations and their integral primitives
give a homotopy equivalence between the tensor exterior complex and R[0].
Identifying this tensor complex with the PD de Rham presentation is a
separate construction.
-/

open _root_.CategoryTheory
open scoped TensorProduct

open OAI.AlgebraicGeometry.Crystalline.Cohomology.Multivariable.DividedAlgebra.MultivariableDividedAlgebra OAI.AlgebraicGeometry.Crystalline.Cohomology.FreeDivided.Derivation.FreeDividedDerivation OAI.AlgebraicGeometry.Crystalline.Cohomology.FreeDivided.Primitive.FreeDividedPrimitive

universe u

variable (R σ : Type u) [CommRing R] [Fintype σ]

local notation "G" => DividedPowerAlgebra R (σ →₀ R)
def derivatives (i : σ) : Module.End R G := (FreeDivided.Derivation.FreeDividedDerivation.derivation R σ i).toLinearMap

local notation "D" => OAI.AlgebraicGeometry.Crystalline.Cohomology.FreeDivided.KoszulHomotopy.FreeDividedKoszulHomotopy.derivatives R σ
local notation "S" => OAI.AlgebraicGeometry.Crystalline.Cohomology.FreeDivided.Primitive.FreeDividedPrimitive.primitive R σ

omit [Fintype σ] in
theorem commute (i j : σ) : Function.Commute (D i) (D j) :=
  FreeDivided.Derivation.FreeDividedDerivation.derivations_commute R σ i j

def complex : CochainComplex (ModuleCat R) ℕ :=
  Koszul.Tensor.KoszulTensor.complex R σ G D (commute R σ)

local notation "C" => OAI.AlgebraicGeometry.Crystalline.Cohomology.FreeDivided.KoszulHomotopy.FreeDividedKoszulHomotopy.complex R σ
local notation "comm" => OAI.AlgebraicGeometry.Crystalline.Cohomology.FreeDivided.KoszulHomotopy.FreeDividedKoszulHomotopy.commute R σ

omit [Fintype σ] in
theorem rightInverse (i : σ) (a : G) : D i (S i a) = a :=
  Primitive.FreeDividedPrimitive.derivation_primitive R σ i a

omit [Fintype σ] in
theorem commute_primitive (i j : σ) (hji : j ≠ i) (a : G) : D j (S i a) = S i (D j a) :=
  LinearMap.congr_fun (Primitive.FreeDividedPrimitive.derivation_primitive_commute R σ i j (Ne.symm hji)) a

omit [Fintype σ] in
theorem coordinateProjection (i : σ) :
    Koszul.CoordinateHomotopy.KoszulCoordinateHomotopy.coefficientProjection R σ G D i (S i) = Primitive.FreeDividedPrimitive.projection R σ i := by
  change LinearMap.id - (S i).comp (D i) = Primitive.FreeDividedPrimitive.projection R σ i
  exact sub_eq_iff_eq_add.mpr ((Primitive.FreeDividedPrimitive.primitive_derivation_linear R σ i).symm.trans (add_comm _ _))

omit [Fintype σ] in
theorem coefficientProjection (l : List σ) :
    Koszul.SuccessiveHomotopy.KoszulSuccessiveHomotopy.coefficient R σ G D S l = Constants.FreeDividedConstants.successive R σ l := by
  induction l with
  | nil => rfl
  | cons i l ih =>
    change (Koszul.SuccessiveHomotopy.KoszulSuccessiveHomotopy.coefficient R σ G D S l).comp
      (Koszul.CoordinateHomotopy.KoszulCoordinateHomotopy.coefficientProjection R σ G D i (S i)) =
        (Constants.FreeDividedConstants.successive R σ l).comp (Primitive.FreeDividedPrimitive.projection R σ i)
    rw [ih, coordinateProjection]

def coordinateList : List σ := Finset.univ.toList

theorem mem_coordinateList (i : σ) : i ∈ coordinateList σ := by
  classical
  exact Finset.mem_toList.mpr (Finset.mem_univ i)

def finalProjection : C ⟶ C :=
  Koszul.SuccessiveHomotopy.KoszulSuccessiveHomotopy.chain R σ G D S comm (coordinateList σ)

def contraction : Homotopy (𝟙 C) (finalProjection R σ) :=
  Koszul.SuccessiveHomotopy.KoszulSuccessiveHomotopy.homotopy R σ G D S comm (coordinateList σ)

theorem finalProjection_positive (n : ℕ) : (finalProjection R σ).f (n + 1) = 0 :=
  Koszul.SuccessiveHomotopy.KoszulSuccessiveHomotopy.chain_positive R σ G D S comm
    (rightInverse R σ) (commute_primitive R σ)
    (coordinateList σ) (mem_coordinateList σ) n

local notation "e₀" => OAI.AlgebraicGeometry.Crystalline.Cohomology.TensorDegree.TensorDegreeZero.equiv R σ G

def inclusionZero : R →ₗ[R] Koszul.Tensor.KoszulTensor.Term R σ G 0 :=
  (e₀).symm.toLinearMap.comp (Constants.FreeDividedConstants.constants R σ)

def retractionZero : Koszul.Tensor.KoszulTensor.Term R σ G 0 →ₗ[R] R :=
  (Constants.FreeDividedConstants.constantCoefficient R σ).comp (e₀).toLinearMap

omit [Fintype σ] in
theorem inclusionZero_apply (r : R) : inclusionZero R σ r =
    algebraMap R G r ⊗ₜ[R] (exteriorPower.zeroEquiv R (σ →₀ R)).symm 1 :=
  TensorDegree.TensorDegreeZero.equiv_symm R σ G (algebraMap R G r)

omit [Fintype σ] in
theorem retraction_inclusion :
    (retractionZero R σ).comp (inclusionZero R σ) = LinearMap.id := by
  apply LinearMap.ext
  intro r
  change Constants.FreeDividedConstants.constantCoefficient R σ
    (e₀ ((e₀).symm (Constants.FreeDividedConstants.constants R σ r))) = r
  rw [LinearEquiv.apply_symm_apply]
  exact LinearMap.congr_fun (Constants.FreeDividedConstants.constantCoefficient_constants R σ) r

theorem finalProjection_zero : (finalProjection R σ).f 0 =
    ModuleCat.ofHom ((inclusionZero R σ).comp (retractionZero R σ)) := by
  have hf := Koszul.SuccessiveHomotopy.KoszulSuccessiveHomotopy.chain_f R σ G D S comm
    (rightInverse R σ) (commute_primitive R σ) (coordinateList σ) 0
  change (finalProjection R σ).f 0 = _ at hf
  rw [coefficientProjection R σ,
    Constants.FreeDividedConstants.successive_eq_constants R σ (coordinateList σ) (mem_coordinateList σ),
    ExteriorCoordinate.ExteriorCoordinateProjection.successive_zero] at hf
  apply hf.trans
  apply ModuleCat.hom_ext
  exact (TensorDegree.TensorDegreeZero.conjugate R σ G
    ((Constants.FreeDividedConstants.constants R σ).comp (Constants.FreeDividedConstants.constantCoefficient R σ))).symm

theorem differential_inclusion :
    (Koszul.Tensor.KoszulTensor.differential R σ G D 0).comp (inclusionZero R σ) = 0 := by
  apply LinearMap.ext
  intro r
  change Koszul.Tensor.KoszulTensor.differential R σ G D 0 (inclusionZero R σ r) = 0
  rw [inclusionZero_apply, Koszul.Tensor.KoszulTensor.differential_tmul]
  apply Finset.sum_eq_zero
  intro i _
  change FreeDivided.Derivation.FreeDividedDerivation.derivation R σ i (algebraMap R G r) ⊗ₜ[R] _ = 0
  rw [Derivation.map_algebraMap, TensorProduct.zero_tmul]

def inclusionHom : ModuleCat.of R R ⟶ (C).X 0 := ModuleCat.ofHom (inclusionZero R σ)

def retractionHom : (C).X 0 ⟶ ModuleCat.of R R := ModuleCat.ofHom (retractionZero R σ)

theorem differential_inclusionHom : inclusionHom R σ ≫ (C).d 0 1 = 0 := by
  apply ModuleCat.hom_ext
  have hd := Koszul.CoordinateHomotopy.KoszulCoordinateHomotopy.complex_d R σ G D comm 0
  exact (congrArg (fun f : (C).X 0 ⟶ (C).X 1 => f.hom.comp (inclusionZero R σ)) hd).trans
    (differential_inclusion R σ)

theorem retraction_inclusionHom : inclusionHom R σ ≫ retractionHom R σ =
    𝟙 (ModuleCat.of R R) := ModuleCat.hom_ext (retraction_inclusion R σ)

theorem inclusion_retractionHom : retractionHom R σ ≫ inclusionHom R σ =
    (finalProjection R σ).f 0 := (finalProjection_zero R σ).symm

/-- The actual divided-polynomial tensor complex contracts onto its constants. -/
def homotopyEquiv : HomotopyEquiv ((CochainComplex.single₀ (ModuleCat R)).obj (ModuleCat.of R R)) C :=
  SingleRetraction.SingleRetractionHomotopy.homotopyEquiv C (ModuleCat.of R R)
    (finalProjection R σ) (contraction R σ)
    (inclusionHom R σ) (retractionHom R σ)
    (differential_inclusionHom R σ) (retraction_inclusionHom R σ)
    (inclusion_retractionHom R σ) (finalProjection_positive R σ)

def augmentation : (CochainComplex.single₀ (ModuleCat R)).obj (ModuleCat.of R R) ⟶ C :=
  (homotopyEquiv R σ).hom

instance augmentation_quasiIso : QuasiIso (augmentation R σ) :=
  HomotopyEquiv.quasiIso_hom (homotopyEquiv R σ)

end

end OAI.AlgebraicGeometry.Crystalline.Cohomology.FreeDivided.KoszulHomotopy.FreeDividedKoszulHomotopy

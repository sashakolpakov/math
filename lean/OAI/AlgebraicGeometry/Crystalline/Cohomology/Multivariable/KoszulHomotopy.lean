import OAI.AlgebraicGeometry.Crystalline.Cohomology.Koszul.SuccessiveHomotopy
import OAI.AlgebraicGeometry.Crystalline.Cohomology.Multivariable.Constants
import OAI.AlgebraicGeometry.Crystalline.Cohomology.TensorDegree
import OAI.AlgebraicGeometry.Crystalline.Cohomology.SingleRetraction
import Mathlib.Algebra.Homology.QuasiIso

/-! # Koszul Homotopy -/

namespace OAI.AlgebraicGeometry.Crystalline.Cohomology.Multivariable.KoszulHomotopy.MultivariableKoszulHomotopy

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

open OAI.AlgebraicGeometry.Crystalline.Cohomology.Multivariable.DividedAlgebra.MultivariableDividedAlgebra OAI.AlgebraicGeometry.Crystalline.Cohomology.Multivariable.CoordinateDerivation.MultivariableCoordinateDerivation OAI.AlgebraicGeometry.Crystalline.Cohomology.Multivariable.Primitive.MultivariablePrimitive

universe u

variable (R σ K : Type u) [CommRing R] [Field K] [CharZero K] [Algebra R K]
  (h : Function.Injective (algebraMap R K))
  (I : Ideal R) (δ : DividedPowers I) (hunit : ∃ a ∈ I, IsUnit (algebraMap R K a)) [Fintype σ]

local notation "G" => DividedPowerAlgebra R (σ →₀ R)
def derivatives (i : σ) : Module.End R G := (CoordinateDerivation.MultivariableCoordinateDerivation.derivation R σ K h I δ hunit i).toLinearMap

local notation "D" => OAI.AlgebraicGeometry.Crystalline.Cohomology.Multivariable.KoszulHomotopy.MultivariableKoszulHomotopy.derivatives R σ K h I δ hunit
local notation "S" => OAI.AlgebraicGeometry.Crystalline.Cohomology.Multivariable.Primitive.MultivariablePrimitive.primitive R σ K h

omit [Fintype σ] in
theorem commute (i j : σ) : Function.Commute (D i) (D j) :=
  CoordinateDerivation.MultivariableCoordinateDerivation.derivations_commute R σ K h I δ hunit i j

def complex : CochainComplex (ModuleCat R) ℕ :=
  Koszul.Tensor.KoszulTensor.complex R σ G D (commute R σ K h I δ hunit)

local notation "C" => OAI.AlgebraicGeometry.Crystalline.Cohomology.Multivariable.KoszulHomotopy.MultivariableKoszulHomotopy.complex R σ K h I δ hunit
local notation "comm" => OAI.AlgebraicGeometry.Crystalline.Cohomology.Multivariable.KoszulHomotopy.MultivariableKoszulHomotopy.commute R σ K h I δ hunit

omit [Fintype σ] in
theorem rightInverse (i : σ) (a : G) : D i (S i a) = a :=
  Primitive.MultivariablePrimitive.derivation_primitive R σ K h I δ hunit i a

omit [Fintype σ] in
theorem commute_primitive (i j : σ) (hji : j ≠ i) (a : G) : D j (S i a) = S i (D j a) :=
  LinearMap.congr_fun (Primitive.MultivariablePrimitive.derivation_primitive_commute R σ K h I δ hunit i j (Ne.symm hji)) a

omit [Fintype σ] in
theorem coordinateProjection (i : σ) :
    Koszul.CoordinateHomotopy.KoszulCoordinateHomotopy.coefficientProjection R σ G D i (S i) = Primitive.MultivariablePrimitive.projection R σ K h i := by
  change LinearMap.id - (S i).comp (D i) = Primitive.MultivariablePrimitive.projection R σ K h i
  exact sub_eq_iff_eq_add.mpr ((Primitive.MultivariablePrimitive.primitive_derivation_linear R σ K h I δ hunit i).symm.trans (add_comm _ _))

omit [Fintype σ] in
theorem coefficientProjection (l : List σ) :
    Koszul.SuccessiveHomotopy.KoszulSuccessiveHomotopy.coefficient R σ G D S l = Constants.MultivariableConstants.successive R σ K h l := by
  induction l with
  | nil => rfl
  | cons i l ih =>
    change (Koszul.SuccessiveHomotopy.KoszulSuccessiveHomotopy.coefficient R σ G D S l).comp
      (Koszul.CoordinateHomotopy.KoszulCoordinateHomotopy.coefficientProjection R σ G D i (S i)) =
        (Constants.MultivariableConstants.successive R σ K h l).comp (Primitive.MultivariablePrimitive.projection R σ K h i)
    rw [ih, coordinateProjection]

def coordinateList : List σ := Finset.univ.toList

theorem mem_coordinateList (i : σ) : i ∈ coordinateList σ := by
  classical
  exact Finset.mem_toList.mpr (Finset.mem_univ i)

def finalProjection : C ⟶ C :=
  Koszul.SuccessiveHomotopy.KoszulSuccessiveHomotopy.chain R σ G D S comm (coordinateList σ)

def contraction : Homotopy (𝟙 C) (finalProjection R σ K h I δ hunit) :=
  Koszul.SuccessiveHomotopy.KoszulSuccessiveHomotopy.homotopy R σ G D S comm (coordinateList σ)

theorem finalProjection_positive (n : ℕ) : (finalProjection R σ K h I δ hunit).f (n + 1) = 0 :=
  Koszul.SuccessiveHomotopy.KoszulSuccessiveHomotopy.chain_positive R σ G D S comm
    (rightInverse R σ K h I δ hunit) (commute_primitive R σ K h I δ hunit)
    (coordinateList σ) (mem_coordinateList σ) n

local notation "e₀" => OAI.AlgebraicGeometry.Crystalline.Cohomology.TensorDegree.TensorDegreeZero.equiv R σ G

def inclusionZero : R →ₗ[R] Koszul.Tensor.KoszulTensor.Term R σ G 0 :=
  (e₀).symm.toLinearMap.comp (Constants.MultivariableConstants.constants R σ)

def retractionZero : Koszul.Tensor.KoszulTensor.Term R σ G 0 →ₗ[R] R :=
  (Constants.MultivariableConstants.constantCoefficient R σ K h).comp (e₀).toLinearMap

omit [Fintype σ] in
theorem inclusionZero_apply (r : R) : inclusionZero R σ r =
    algebraMap R G r ⊗ₜ[R] (exteriorPower.zeroEquiv R (σ →₀ R)).symm 1 :=
  TensorDegree.TensorDegreeZero.equiv_symm R σ G (algebraMap R G r)

omit [Fintype σ] in
theorem retraction_inclusion :
    (retractionZero R σ K h).comp (inclusionZero R σ) = LinearMap.id := by
  apply LinearMap.ext
  intro r
  change Constants.MultivariableConstants.constantCoefficient R σ K h
    (e₀ ((e₀).symm (Constants.MultivariableConstants.constants R σ r))) = r
  rw [LinearEquiv.apply_symm_apply]
  exact LinearMap.congr_fun (Constants.MultivariableConstants.constantCoefficient_constants R σ K h) r

theorem finalProjection_zero : (finalProjection R σ K h I δ hunit).f 0 =
    ModuleCat.ofHom ((inclusionZero R σ).comp (retractionZero R σ K h)) := by
  have hf := Koszul.SuccessiveHomotopy.KoszulSuccessiveHomotopy.chain_f R σ G D S comm
    (rightInverse R σ K h I δ hunit) (commute_primitive R σ K h I δ hunit) (coordinateList σ) 0
  change (finalProjection R σ K h I δ hunit).f 0 = _ at hf
  rw [coefficientProjection R σ K h I δ hunit,
    Constants.MultivariableConstants.successive_eq_constants R σ K h (coordinateList σ) (mem_coordinateList σ),
    ExteriorCoordinate.ExteriorCoordinateProjection.successive_zero] at hf
  apply hf.trans
  apply ModuleCat.hom_ext
  exact (TensorDegree.TensorDegreeZero.conjugate R σ G
    ((Constants.MultivariableConstants.constants R σ).comp (Constants.MultivariableConstants.constantCoefficient R σ K h))).symm

theorem differential_inclusion :
    (Koszul.Tensor.KoszulTensor.differential R σ G D 0).comp (inclusionZero R σ) = 0 := by
  apply LinearMap.ext
  intro r
  change Koszul.Tensor.KoszulTensor.differential R σ G D 0 (inclusionZero R σ r) = 0
  rw [inclusionZero_apply, Koszul.Tensor.KoszulTensor.differential_tmul]
  apply Finset.sum_eq_zero
  intro i _
  change CoordinateDerivation.MultivariableCoordinateDerivation.derivation R σ K h I δ hunit i (algebraMap R G r) ⊗ₜ[R] _ = 0
  rw [Derivation.map_algebraMap, TensorProduct.zero_tmul]

def inclusionHom : ModuleCat.of R R ⟶ (C).X 0 := ModuleCat.ofHom (inclusionZero R σ)

def retractionHom : (C).X 0 ⟶ ModuleCat.of R R := ModuleCat.ofHom (retractionZero R σ K h)

theorem differential_inclusionHom : inclusionHom R σ K h I δ hunit ≫ (C).d 0 1 = 0 := by
  apply ModuleCat.hom_ext
  have hd := Koszul.CoordinateHomotopy.KoszulCoordinateHomotopy.complex_d R σ G D comm 0
  exact (congrArg (fun f : (C).X 0 ⟶ (C).X 1 => f.hom.comp (inclusionZero R σ)) hd).trans
    (differential_inclusion R σ K h I δ hunit)

theorem retraction_inclusionHom : inclusionHom R σ K h I δ hunit ≫ retractionHom R σ K h I δ hunit =
    𝟙 (ModuleCat.of R R) := ModuleCat.hom_ext (retraction_inclusion R σ K h)

theorem inclusion_retractionHom : retractionHom R σ K h I δ hunit ≫ inclusionHom R σ K h I δ hunit =
    (finalProjection R σ K h I δ hunit).f 0 := (finalProjection_zero R σ K h I δ hunit).symm

/-- The actual divided-polynomial tensor complex contracts onto its constants. -/
def homotopyEquiv : HomotopyEquiv ((CochainComplex.single₀ (ModuleCat R)).obj (ModuleCat.of R R)) C :=
  SingleRetraction.SingleRetractionHomotopy.homotopyEquiv C (ModuleCat.of R R)
    (finalProjection R σ K h I δ hunit) (contraction R σ K h I δ hunit)
    (inclusionHom R σ K h I δ hunit) (retractionHom R σ K h I δ hunit)
    (differential_inclusionHom R σ K h I δ hunit) (retraction_inclusionHom R σ K h I δ hunit)
    (inclusion_retractionHom R σ K h I δ hunit) (finalProjection_positive R σ K h I δ hunit)

def augmentation : (CochainComplex.single₀ (ModuleCat R)).obj (ModuleCat.of R R) ⟶ C :=
  (homotopyEquiv R σ K h I δ hunit).hom

instance augmentation_quasiIso : QuasiIso (augmentation R σ K h I δ hunit) :=
  HomotopyEquiv.quasiIso_hom (homotopyEquiv R σ K h I δ hunit)

end

end OAI.AlgebraicGeometry.Crystalline.Cohomology.Multivariable.KoszulHomotopy.MultivariableKoszulHomotopy

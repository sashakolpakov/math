import OAI.AlgebraicGeometry.ComplexMultiplication.ScalarDescent
import Mathlib.LinearAlgebra.ExteriorPower.Basis
import Mathlib.LinearAlgebra.TensorProduct.Basis
import Mathlib.LinearAlgebra.TensorProduct.Tower
import Mathlib.LinearAlgebra.TensorProduct.Pi
import Mathlib.Algebra.Module.Rat

/-! # Exterior Base Change -/

namespace OAI.AlgebraicGeometry.ComplexMultiplication.ExteriorBaseChange.CM

noncomputable section

/-!
# Coefficient extension of rational exterior powers

The map from `K ⊗[ℚ] ⋀[ℚ]^n U` to `⋀[K]^n (K ⊗[ℚ] U)` is defined by
the universal properties of exterior powers and tensor products. Its
bijectivity is proved by comparing the exterior bases of a rational basis.
Thus coefficient conjugation in higher degree remains the actual action
on the scalar factor of the rational exterior power.
-/

open scoped TensorProduct Classical

variable (K : Type*) [Field K] [Algebra ℚ K]
variable (U : Type*) [AddCommGroup U] [Module ℚ U] (n : ℕ)

/-- Wedge rational vectors after their canonical inclusion into the scalar extension. -/
def rationalExteriorProduct : U [⋀^Fin n]→ₗ[ℚ] (⋀[K]^n (K ⊗[ℚ] U)) where
  __ := ((exteriorPower.ιMulti K n).toMultilinearMap.restrictScalars ℚ).compLinearMap
    (fun _ => TensorProduct.mk ℚ K U 1)
  map_eq_zero_of_eq' _v _i _j hij hne :=
    (exteriorPower.ιMulti K n).map_eq_zero_of_eq _
      (congrArg (fun u : U => (1 : K) ⊗ₜ[ℚ] u) hij) hne

/-- The canonical rational map from exterior powers before and after extending coefficients. -/
def rationalExteriorInclusion : (⋀[ℚ]^n U) →ₗ[ℚ] (⋀[K]^n (K ⊗[ℚ] U)) :=
  exteriorPower.alternatingMapLinearEquiv (rationalExteriorProduct K U n)

@[simp]
theorem rationalExteriorInclusion_ιMulti (v : Fin n → U) :
    rationalExteriorInclusion K U n (exteriorPower.ιMulti ℚ n v) =
      exteriorPower.ιMulti K n (fun i => (1 : K) ⊗ₜ[ℚ] v i) := by
  rw [rationalExteriorInclusion, exteriorPower.alternatingMapLinearEquiv_apply_ιMulti]
  rfl

/-- The canonical coefficient-extension map for the `n`th exterior power. -/
def exteriorBaseChange : K ⊗[ℚ] (⋀[ℚ]^n U) →ₗ[K] (⋀[K]^n (K ⊗[ℚ] U)) :=
  (rationalExteriorInclusion K U n).liftBaseChange K

@[simp]
theorem exteriorBaseChange_tmul_ιMulti (a : K) (v : Fin n → U) :
    exteriorBaseChange K U n (a ⊗ₜ[ℚ] exteriorPower.ιMulti ℚ n v) =
      a • exteriorPower.ιMulti K n (fun i => (1 : K) ⊗ₜ[ℚ] v i) := by
  simp [exteriorBaseChange]

/-- In a scalar-extended rational basis, conjugation acts on each coefficient. -/
theorem baseChangeBasis_repr_scalarConjugate {κ : Type*} (b : Module.Basis κ ℚ U)
    (g : Gal(K/ℚ)) (x : K ⊗[ℚ] U) (i : κ) :
    (b.baseChange K).repr (ScalarDescent.CM.scalarConjugate ℚ K U g x) i =
      g ((b.baseChange K).repr x i) := by
  induction x using TensorProduct.inductionOn with
  | tmul a u => simp
  | add x y hx hy => simp [hx, hy]

/-- Mapping coefficient fields maps the coordinates in a rational basis. -/
theorem baseChangeBasis_repr_coefficientMap {L : Type*} [Field L] [Algebra ℚ L]
    {κ : Type*} (b : Module.Basis κ ℚ U) (φ : K →ₐ[ℚ] L) (x : K ⊗[ℚ] U) (i : κ) :
    (b.baseChange L).repr (TensorProduct.map φ.toLinearMap LinearMap.id x) i =
      φ ((b.baseChange K).repr x i) := by
  induction x using TensorProduct.inductionOn with
  | tmul a u => simp
  | add x y hx hy => simp [hx, hy]

variable {ι : Type*} [LinearOrder ι] (b : Module.Basis ι ℚ U)

/-- The canonical map takes the scalar-extended rational exterior basis to the
exterior basis of the scalar-extended degree-one basis. -/
theorem exteriorBaseChange_basis (s : Set.powersetCard ι n) :
    exteriorBaseChange K U n ((b.exteriorPower n).baseChange K s) =
      (b.baseChange K).exteriorPower n s := by
  simp only [Module.Basis.baseChange_apply, exteriorPower.basis_apply,
    exteriorPower.ιMulti_family, exteriorBaseChange_tmul_ιMulti, one_smul, Function.comp_apply]
  apply congrArg (exteriorPower.ιMulti K n)
  funext i
  exact (Module.Basis.baseChange_apply K b _).symm

theorem exteriorBaseChange_eq_basisEquiv :
    exteriorBaseChange K U n =
      ((b.exteriorPower n).baseChange K).equiv ((b.baseChange K).exteriorPower n)
        (Equiv.refl _) := by
  apply ((b.exteriorPower n).baseChange K).ext
  intro s
  change exteriorBaseChange K U n ((b.exteriorPower n).baseChange K s) =
    ((b.exteriorPower n).baseChange K).equiv ((b.baseChange K).exteriorPower n)
      (Equiv.refl _) ((b.exteriorPower n).baseChange K s)
  rw [Module.Basis.equiv_apply, Equiv.refl_apply]
  exact exteriorBaseChange_basis K U n b s

/-- The comparison preserves the coordinates in the corresponding exterior bases. -/
theorem exteriorBaseChange_repr (x : K ⊗[ℚ] (⋀[ℚ]^n U)) (s : Set.powersetCard ι n) :
    ((b.baseChange K).exteriorPower n).repr (exteriorBaseChange K U n x) s =
      ((b.exteriorPower n).baseChange K).repr x s := by
  rw [exteriorBaseChange_eq_basisEquiv K U n b]
  simp only [Module.Basis.equiv, Equiv.refl_symm, Module.Basis.reindex_refl,
    LinearEquiv.coe_coe, LinearEquiv.trans_apply, LinearEquiv.apply_symm_apply]

/-- Coefficient extension commutes with exterior powers in every degree. -/
theorem exteriorBaseChange_bijective : Function.Bijective (exteriorBaseChange K U n) := by
  let : LinearOrder (Module.Free.ChooseBasisIndex ℚ U) := linearOrderOfSTO WellOrderingRel
  rw [exteriorBaseChange_eq_basisEquiv K U n (Module.Free.chooseBasis ℚ U)]
  exact LinearEquiv.bijective _

/-- The canonical comparison, as an isomorphism rather than an assumed identification. -/
def exteriorBaseChangeEquiv : K ⊗[ℚ] (⋀[ℚ]^n U) ≃ₗ[K] (⋀[K]^n (K ⊗[ℚ] U)) :=
  LinearEquiv.ofBijective (exteriorBaseChange K U n) (exteriorBaseChange_bijective K U n)

@[simp]
theorem exteriorBaseChangeEquiv_apply (x : K ⊗[ℚ] (⋀[ℚ]^n U)) :
    exteriorBaseChangeEquiv K U n x = exteriorBaseChange K U n x := rfl

/-- The inverse comparison has the same corresponding exterior coordinates. -/
theorem exteriorBaseChangeEquiv_symm_repr (x : ⋀[K]^n (K ⊗[ℚ] U))
    (s : Set.powersetCard ι n) :
    ((b.exteriorPower n).baseChange K).repr ((exteriorBaseChangeEquiv K U n).symm x) s =
      ((b.baseChange K).exteriorPower n).repr x s := by
  simpa only [← exteriorBaseChangeEquiv_apply, LinearEquiv.apply_symm_apply] using
    (exteriorBaseChange_repr K U n b ((exteriorBaseChangeEquiv K U n).symm x) s).symm

/-- The coefficients of a wedge are the actual determinant coordinates. -/
theorem exteriorBaseChangeEquiv_symm_ιMulti_repr (v : Fin n → K ⊗[ℚ] U)
    (s : Set.powersetCard ι n) :
    ((b.exteriorPower n).baseChange K).repr
        ((exteriorBaseChangeEquiv K U n).symm (exteriorPower.ιMulti K n v)) s =
      (Matrix.of fun i j => (b.baseChange K).repr (v i)
        (Set.powersetCard.ofFinEmbEquiv.symm s j)).det := by
  rw [exteriorBaseChangeEquiv_symm_repr, exteriorPower.basis_repr_apply,
    exteriorPower.ιMultiDual_apply_ιMulti]
  rfl

/-- The exterior comparison is natural under maps of coefficient fields. -/
theorem coefficientMap_exteriorProduct {L : Type*} [Field L] [Algebra ℚ L]
    (φ : K →ₐ[ℚ] L) (v : Fin n → K ⊗[ℚ] U) :
    TensorProduct.map φ.toLinearMap (LinearMap.id : (⋀[ℚ]^n U) →ₗ[ℚ] (⋀[ℚ]^n U))
        ((exteriorBaseChangeEquiv K U n).symm (exteriorPower.ιMulti K n v)) =
      (exteriorBaseChangeEquiv L U n).symm
        (exteriorPower.ιMulti L n
          (fun i => TensorProduct.map φ.toLinearMap LinearMap.id (v i))) := by
  let : LinearOrder (Module.Free.ChooseBasisIndex ℚ U) := linearOrderOfSTO WellOrderingRel
  let b := Module.Free.chooseBasis ℚ U
  apply ((b.exteriorPower n).baseChange L).ext_elem
  intro s
  rw [baseChangeBasis_repr_coefficientMap,
    exteriorBaseChangeEquiv_symm_ιMulti_repr, exteriorBaseChangeEquiv_symm_ιMulti_repr]
  simp only [baseChangeBasis_repr_coefficientMap]
  exact φ.map_det _

/-- Scalar conjugation of an exterior product conjugates each of its factors.
This is proved on the actual scalar extension of the rational exterior power. -/
theorem scalarConjugate_exteriorProduct (g : Gal(K/ℚ)) (v : Fin n → K ⊗[ℚ] U) :
    ScalarDescent.CM.scalarConjugate ℚ K (⋀[ℚ]^n U) g
        ((exteriorBaseChangeEquiv K U n).symm (exteriorPower.ιMulti K n v)) =
      (exteriorBaseChangeEquiv K U n).symm
        (exteriorPower.ιMulti K n (fun i => ScalarDescent.CM.scalarConjugate ℚ K U g (v i))) :=
  coefficientMap_exteriorProduct K U n g.toAlgHom v

end

end OAI.AlgebraicGeometry.ComplexMultiplication.ExteriorBaseChange.CM

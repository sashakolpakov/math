import OAI.AlgebraicGeometry.CycleClass.Geometric.PuncturedLinearHomotopy
import OAI.AlgebraicGeometry.CycleClass.Geometric.ComplexLinearHomotopy
import OAI.AlgebraicGeometry.CycleClass.Geometric.RelativeHomologyExact

/-! # Complex Linear Punctured Homotopy -/

namespace OAI.AlgebraicGeometry.CycleClass.Geometric.ComplexLinearPuncturedHomotopy.Cycles

noncomputable section

/-!
# Complex linear changes act trivially on local homology

Every invertible complex matrix is joined to the identity through invertible
matrices. The induced homotopy on the punctured normal space proves equality
on singular homology. Naturality of the actual connecting boundary of the
pair then gives equality on local homology in degrees at least two.

The result concerns the map induced by the actual linear map of pairs. It
does not assume that a local homology group is cyclic or choose an orientation
generator. General homotopy invariance for arbitrary pairs is not claimed.
-/

open _root_.CategoryTheory _root_.AlgebraicTopology
open scoped _root_.Matrix

variable {n : Type} [Fintype n]

/-- The actual continuous linear map associated to a complex matrix. -/
def complexMatrixMap (A : Matrix n n ℂ) : C(n → ℂ, n → ℂ) where
  toFun := A.mulVec
  continuous_toFun := continuous_const.matrix_mulVec continuous_id

@[simp] theorem complexMatrixMap_apply (A : Matrix n n ℂ) (x : n → ℂ) :
    complexMatrixMap A x = A *ᵥ x := rfl

variable [DecidableEq n]

/-- Invertibility makes the linear map a map of punctured-space pairs. -/
theorem complexMatrixMap_preservesPuncture (A : Matrix n n ℂ) (hA : IsUnit A) :
    Set.MapsTo (TopCat.ofHom (complexMatrixMap A))
      ({0}ᶜ : Set (n → ℂ)) ({0}ᶜ : Set (n → ℂ)) :=
  fun _ hx => PuncturedLinearHomotopy.Cycles.complexMatrix_mulVec_ne_zero A hA hx

@[simp] theorem subspaceMap_complexMatrixMap (A : Matrix n n ℂ) (hA : IsUnit A) :
    LocalHomology.Cycles.subspaceMap (TopCat.ofHom (complexMatrixMap A)) (complexMatrixMap_preservesPuncture A hA) =
      TopCat.ofHom (PuncturedLinearHomotopy.Cycles.complexPuncturedMap A hA) := rfl

/-- A concrete homotopy of the punctured normal space from the identity to
an arbitrary invertible complex linear change of coordinates. -/
def complexPuncturedHomotopy (A : Matrix n n ℂ) (hA : IsUnit A) :
    ContinuousMap.Homotopy (ContinuousMap.id (NormalSphere.Cycles.PuncturedNormal (n → ℂ)))
      (PuncturedLinearHomotopy.Cycles.complexPuncturedMap A hA) :=
  PuncturedLinearHomotopy.Cycles.puncturedHomotopyOfMatrixPath A hA (ComplexLinearHomotopy.Cycles.complexMatrixPath A hA)
    (ComplexLinearHomotopy.Cycles.complexMatrixPath_isUnit A hA)

/-- Every invertible complex linear coordinate change acts as the identity
on genuine singular homology of the punctured normal space. -/
theorem complexPunctured_homologyMap_eq_id
    {R : Type} [Ring R] (M : ModuleCat.{0} R)
    (A : Matrix n n ℂ) (hA : IsUnit A) (k : ℕ) :
    HomologicalComplex.homologyMap
      (((singularChainComplexFunctor (ModuleCat.{0} R)).obj M).map
        (TopCat.ofHom (PuncturedLinearHomotopy.Cycles.complexPuncturedMap A hA))) k =
      𝟙 ((((singularChainComplexFunctor (ModuleCat.{0} R)).obj M).obj
        (TopCat.of (NormalSphere.Cycles.PuncturedNormal (n → ℂ)))).homology k) :=
  PuncturedLinearHomotopy.Cycles.puncturedMatrixPath_homologyMap_eq_id M A hA (ComplexLinearHomotopy.Cycles.complexMatrixPath A hA)
    (ComplexLinearHomotopy.Cycles.complexMatrixPath_isUnit A hA) k

/-- The map on actual local integral homology induced by an invertible
complex matrix, viewed as a map of the pair `(C^n, C^n \ {0})`. -/
def complexMatrixLocalHomologyMap (A : Matrix n n ℂ) (hA : IsUnit A) (k : ℕ) :
    LocalHomology.Cycles.localSingularHomology (TopCat.of (n → ℂ)) 0 k ⟶
      LocalHomology.Cycles.localSingularHomology (TopCat.of (n → ℂ)) 0 k :=
  LocalHomology.Cycles.relativeSingularHomologyMap (TopCat.ofHom (complexMatrixMap A))
    (complexMatrixMap_preservesPuncture A hA) k

/-- In local degrees `k+1 ≥ 2`, the actual induced local map is the identity.
This follows from boundary naturality and the proved ambient contractibility. -/
theorem complexMatrixLocalHomologyMap_succ_eq_id
    (A : Matrix n n ℂ) (hA : IsUnit A) (k : ℕ) (hk : k ≠ 0) :
    complexMatrixLocalHomologyMap A hA (k + 1) =
      𝟙 (LocalHomology.Cycles.localSingularHomology (TopCat.of (n → ℂ)) 0 (k + 1)) := by
  let X := TopCat.of (n → ℂ)
  let U : Set X := {0}ᶜ
  let e := RelativeHomologyExact.Cycles.relativeHomologyBoundaryIso X U k
    (ContractibleModel.Cycles.isZero_integralSingularHomology_of_contractible X (k + 1) (Nat.succ_ne_zero k))
    (ContractibleModel.Cycles.isZero_integralSingularHomology_of_contractible X k hk)
  apply (cancel_mono e.hom).mp
  rw [Category.id_comp]
  change LocalHomology.Cycles.relativeSingularHomologyMap (TopCat.ofHom (complexMatrixMap A))
      (complexMatrixMap_preservesPuncture A hA) (k + 1) ≫
      RelativeHomologyExact.Cycles.relativeHomologyBoundary X U k = RelativeHomologyExact.Cycles.relativeHomologyBoundary X U k
  have h := RelativeHomologyExact.Cycles.relativeHomologyBoundary_naturality
    (TopCat.ofHom (complexMatrixMap A)) (complexMatrixMap_preservesPuncture A hA) k
  rw [subspaceMap_complexMatrixMap A hA] at h
  have hp := complexPunctured_homologyMap_eq_id (ModuleCat.of ℤ ℤ) A hA k
  change RelativeHomologyExact.Cycles.integralSingularHomologyMap (TopCat.ofHom (PuncturedLinearHomotopy.Cycles.complexPuncturedMap A hA)) k = 𝟙 _ at hp
  rw [hp, Category.comp_id] at h
  exact h.symm

/-- Degree-independent form of complex linear invariance above degree one. -/
theorem complexMatrixLocalHomologyMap_eq_id
    (A : Matrix n n ℂ) (hA : IsUnit A) (k : ℕ) (hk : 1 < k) :
    complexMatrixLocalHomologyMap A hA k =
      𝟙 (LocalHomology.Cycles.localSingularHomology (TopCat.of (n → ℂ)) 0 k) := by
  cases k with
  | zero => exact (Nat.not_lt_zero 1 hk).elim
  | succ k =>
    apply complexMatrixLocalHomologyMap_succ_eq_id A hA k
    intro hzero
    subst k
    exact (Nat.lt_irrefl 1) hk

/-- In positive complex dimension, complex linear coordinate changes fix
the entire local homology group in the real orientation degree. -/
theorem complexMatrixLocalHomologyMap_orientationDegree_eq_id
    (p : ℕ) (hp : 0 < p) (A : Matrix (Fin p) (Fin p) ℂ) (hA : IsUnit A) :
    complexMatrixLocalHomologyMap A hA (2 * p) =
      𝟙 (LocalHomology.Cycles.localSingularHomology (TopCat.of (Fin p → ℂ)) 0 (2 * p)) := by
  apply complexMatrixLocalHomologyMap_eq_id A hA (2 * p)
  have hle : 2 ≤ 2 * p := by
    simpa only [Nat.mul_one] using Nat.mul_le_mul_left 2 (Nat.succ_le_of_lt hp)
  exact lt_of_lt_of_le (by decide : 1 < 2) hle

end

end OAI.AlgebraicGeometry.CycleClass.Geometric.ComplexLinearPuncturedHomotopy.Cycles

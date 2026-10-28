import OAI.AlgebraicGeometry.CycleClass.Geometric.NormalSphere
import OAI.AlgebraicGeometry.CycleClass.Geometric.ContractibleModel
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.Topology.Instances.Matrix

/-! # Punctured Linear Homotopy -/

namespace OAI.AlgebraicGeometry.CycleClass.Geometric.PuncturedLinearHomotopy.Cycles

noncomputable section

/-!
# Paths of invertible matrices act homotopically on punctured normal spaces

An actual path through invertible matrices gives an actual continuous homotopy
on the complement of zero. Consequently the induced maps on genuine singular
homology agree. No orientation or relative homology generator is assumed.
-/

open _root_.CategoryTheory _root_.AlgebraicTopology
open scoped _root_.Matrix

variable {n : Type} [Fintype n] [DecidableEq n]

/-- An invertible complex matrix cannot send a nonzero vector to zero. -/
theorem complexMatrix_mulVec_ne_zero (A : Matrix n n ℂ) (hA : IsUnit A)
    {x : n → ℂ} (hx : x ≠ 0) : A *ᵥ x ≠ 0 := by
  intro hz
  apply hx
  apply Matrix.mulVec_injective_of_isUnit hA
  simpa only [Matrix.mulVec_zero] using hz

/-- The continuous map of the actual punctured vector space induced by an
invertible complex matrix. -/
def complexPuncturedMap (A : Matrix n n ℂ) (hA : IsUnit A) :
    C(NormalSphere.Cycles.PuncturedNormal (n → ℂ), NormalSphere.Cycles.PuncturedNormal (n → ℂ)) where
  toFun x := ⟨A *ᵥ x.1, complexMatrix_mulVec_ne_zero A hA x.2⟩
  continuous_toFun :=
    (continuous_const.matrix_mulVec continuous_subtype_val).subtype_mk _

@[simp] theorem complexPuncturedMap_coe (A : Matrix n n ℂ) (hA : IsUnit A)
    (x : NormalSphere.Cycles.PuncturedNormal (n → ℂ)) :
    (complexPuncturedMap A hA x).1 = A *ᵥ x.1 := rfl

@[simp] theorem complexPuncturedMap_one :
    complexPuncturedMap (1 : Matrix n n ℂ) isUnit_one =
      ContinuousMap.id (NormalSphere.Cycles.PuncturedNormal (n → ℂ)) := by
  ext x i
  simp

/-- Any path of invertible matrices from the identity to `A` induces a
homotopy from the identity of the punctured space to multiplication by `A`. -/
def puncturedHomotopyOfMatrixPath (A : Matrix n n ℂ) (hA : IsUnit A)
    (P : Path (1 : Matrix n n ℂ) A) (hP : ∀ t, IsUnit (P t)) :
    ContinuousMap.Homotopy (ContinuousMap.id (NormalSphere.Cycles.PuncturedNormal (n → ℂ)))
      (complexPuncturedMap A hA) where
  toFun q := complexPuncturedMap (P q.1) (hP q.1) q.2
  continuous_toFun :=
    ((P.continuous.comp continuous_fst).matrix_mulVec
      (continuous_subtype_val.comp continuous_snd)).subtype_mk _
  map_zero_left x := by
    apply Subtype.ext
    change P 0 *ᵥ x.1 = x.1
    simp
  map_one_left x := by
    apply Subtype.ext
    change P 1 *ᵥ x.1 = A *ᵥ x.1
    rw [P.target]

theorem puncturedHomotopyOfMatrixPath_apply (A : Matrix n n ℂ) (hA : IsUnit A)
    (P : Path (1 : Matrix n n ℂ) A) (hP : ∀ t, IsUnit (P t))
    (t : unitInterval) (x : NormalSphere.Cycles.PuncturedNormal (n → ℂ)) :
    (puncturedHomotopyOfMatrixPath A hA P hP (t, x)).1 = P t *ᵥ x.1 := rfl

/-- On genuine singular homology, the map from the endpoint of an invertible
matrix path based at the identity is the identity map in every degree. -/
theorem puncturedMatrixPath_homologyMap_eq_id
    {R : Type} [Ring R] (M : ModuleCat.{0} R)
    (A : Matrix n n ℂ) (hA : IsUnit A)
    (P : Path (1 : Matrix n n ℂ) A) (hP : ∀ t, IsUnit (P t)) (k : ℕ) :
    HomologicalComplex.homologyMap
      (((singularChainComplexFunctor (ModuleCat.{0} R)).obj M).map
        (TopCat.ofHom (complexPuncturedMap A hA))) k =
      𝟙 ((((singularChainComplexFunctor (ModuleCat.{0} R)).obj M).obj
        (TopCat.of (NormalSphere.Cycles.PuncturedNormal (n → ℂ)))).homology k) := by
  have H : TopCat.Homotopy
      (𝟙 (TopCat.of (NormalSphere.Cycles.PuncturedNormal (n → ℂ))))
      (TopCat.ofHom (complexPuncturedMap A hA)) :=
    puncturedHomotopyOfMatrixPath A hA P hP
  simpa only [CategoryTheory.Functor.map_id, HomologicalComplex.homologyMap_id] using
    (H.congr_homologyMap_singularChainComplexFunctor M k).symm

end

end OAI.AlgebraicGeometry.CycleClass.Geometric.PuncturedLinearHomotopy.Cycles

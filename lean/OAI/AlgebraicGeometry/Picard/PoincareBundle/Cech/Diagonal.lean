import OAI.AlgebraicGeometry.Picard.PoincareBundle.Cech.Switch

/-! # Diagonal -/

namespace OAI.AlgebraicGeometry.Picard.PoincareBundle.Cech.Diagonal

noncomputable section

/-!
# The actual diagonal compatibility of affine gluing implies the switch diagonal law
-/

open _root_.CategoryTheory _root_.ModuleCat TensorProduct
open scoped TensorProduct ChangeOfRings

universe u

open OAI.AlgebraicGeometry.Picard.PoincareBundle.Cech.ModuleModels OAI.AlgebraicGeometry.Picard.PoincareBundle.Cech.Switch

variable (R S : Type u) [CommRing R] [CommRing S] [Algebra R S]

/-- The coordinate map of the actual affine diagonal. -/
def diagonalMap : S ⊗[R] S →+* S := (Algebra.TensorProduct.lmul' R).toRingHom

variable (M : ModuleCat.{u} S)

/-- The identity map after restricting scalars along a projection and the diagonal. -/
def diagonalInput (i : S →+* S ⊗[R] S) (hi : ∀ s, diagonalMap R S (i s) = s) :
    M ⟶ (restrictScalars i).obj ((restrictScalars (diagonalMap R S)).obj M) :=
  ofHom (Y := (restrictScalars i).obj ((restrictScalars (diagonalMap R S)).obj M)) {
    toFun := fun m => m
    map_add' := fun _ _ => rfl
    map_smul' := fun s m => by
      change s • m = diagonalMap R S (i s) • m
      rw [hi] }

/-- Evaluation on the diagonal, as a morphism of actual tensor-ring modules. -/
def evaluation (i : S →+* S ⊗[R] S) (hi : ∀ s, diagonalMap R S (i s) = s) :
    (extendScalars i).obj M ⟶ (restrictScalars (diagonalMap R S)).obj M :=
  ((extendRestrictScalarsAdj i).homEquiv _ _).symm (diagonalInput R S M i hi)

@[simp]
theorem evaluation_tmul (i : S →+* S ⊗[R] S)
    (hi : ∀ s, diagonalMap R S (i s) = s) (x : S ⊗[R] S) (m : M) :
    evaluation R S M i hi (x ⊗ₜ[S,i] m) =
      (show (restrictScalars (diagonalMap R S)).obj M from diagonalMap R S x • m) := rfl

/-- Evaluation of the first pullback on the diagonal. -/
def firstEvaluation : ModuleModels.firstPullback R S M ⟶ (restrictScalars (diagonalMap R S)).obj M :=
  evaluation R S M (ModuleModels.firstMap R S) (fun s => mul_one s)

/-- Evaluation of the second pullback on the diagonal. -/
def secondEvaluation : ModuleModels.secondPullback R S M ⟶ (restrictScalars (diagonalMap R S)).obj M :=
  evaluation R S M (ModuleModels.secondMap R S) (fun s => one_mul s)

/-- The first tensor model identifies geometric diagonal evaluation with scalar multiplication. -/
theorem diagonal_firstModel (z : ModuleModels.firstPullback R S M) :
    DescentSwitch.diagonal R S ((restrictScalars (algebraMap R S)).obj M)
        (ModuleModels.firstModel R S M z) =
      (show (restrictScalars (algebraMap R S)).obj M from firstEvaluation R S M z) := by
  induction z using TensorProduct.inductionOn with
  | add x y hx hy =>
      erw [map_add, map_add, hx, hy, map_add]
      rfl
  | tmul x m =>
      induction x using TensorProduct.inductionOn with
      | add x y hx hy =>
          erw [add_tmul, map_add, map_add, hx, hy, map_add]
          rfl
      | tmul s t =>
          erw [ModuleModels.firstModel_tmul, DescentSwitch.diagonal_tmul]
          change t • (s • m) = (s * t) • m
          rw [← mul_smul, mul_comm]

/-- The second tensor model identifies geometric diagonal evaluation with scalar multiplication. -/
theorem diagonal_secondModel (z : ModuleModels.secondPullback R S M) :
    DescentSwitch.diagonal R S ((restrictScalars (algebraMap R S)).obj M)
        (ModuleModels.secondModel R S M z) =
      (show (restrictScalars (algebraMap R S)).obj M from secondEvaluation R S M z) := by
  induction z using TensorProduct.inductionOn with
  | add x y hx hy =>
      erw [map_add, map_add, hx, hy, map_add]
      rfl
  | tmul x m =>
      induction x using TensorProduct.inductionOn with
      | add x y hx hy =>
          erw [add_tmul, map_add, map_add, hx, hy, map_add]
          rfl
      | tmul s t =>
          erw [ModuleModels.secondModel_tmul, DescentSwitch.diagonal_tmul]
          exact (mul_smul s t m).symm

/-- Compatibility of the actual gluing isomorphism with the diagonal gives the switch law. -/
theorem gluingSwitch_diagonal (σ : ModuleModels.firstPullback R S M ≅ ModuleModels.secondPullback R S M)
    (h : σ.hom ≫ secondEvaluation R S M = firstEvaluation R S M)
    (z : S ⊗[R] (restrictScalars (algebraMap R S)).obj M) :
    DescentSwitch.diagonal R S ((restrictScalars (algebraMap R S)).obj M)
        (Switch.gluingSwitch R S M σ z) =
      DescentSwitch.diagonal R S ((restrictScalars (algebraMap R S)).obj M) z := by
  have hh := ConcreteCategory.congr_hom h ((ModuleModels.firstModel R S M).symm z)
  calc
    _ = (show (restrictScalars (algebraMap R S)).obj M from
        secondEvaluation R S M (σ.hom ((ModuleModels.firstModel R S M).symm z))) :=
      diagonal_secondModel R S M _
    _ = (show (restrictScalars (algebraMap R S)).obj M from
        firstEvaluation R S M ((ModuleModels.firstModel R S M).symm z)) := hh
    _ = DescentSwitch.diagonal R S ((restrictScalars (algebraMap R S)).obj M)
        (ModuleModels.firstModel R S M ((ModuleModels.firstModel R S M).symm z)) :=
      (diagonal_firstModel R S M _).symm
    _ = _ := by rw [AddEquiv.apply_symm_apply]

end

end OAI.AlgebraicGeometry.Picard.PoincareBundle.Cech.Diagonal

import OAI.AlgebraicGeometry.Picard.PoincareBundle.Cech.ThirdModel
import OAI.AlgebraicGeometry.Picard.PoincareBundle.ModuleBaseChangeCoordinates

/-! # Flat Coordinates -/

namespace OAI.AlgebraicGeometry.Picard.PoincareBundle.Cech.FlatCoordinates

noncomputable section

/-!
# Pure tensors in the flattened affine triple-product models
-/

open _root_.CategoryTheory _root_.ModuleCat TensorProduct
open scoped TensorProduct ChangeOfRings

universe u

open OAI.AlgebraicGeometry.Picard.PoincareBundle.Cech.ModuleModels OAI.AlgebraicGeometry.Picard.PoincareBundle.Cech.TripleGluing OAI.AlgebraicGeometry.Picard.PoincareBundle.Cech.TripleExtension
open OAI.AlgebraicGeometry.Picard.PoincareBundle.ExtensionComposition OAI.AlgebraicGeometry.Picard.PoincareBundle.ModuleBaseChangeFunctor OAI.AlgebraicGeometry.Picard.PoincareBundle.ModuleBaseChangeCoordinates

variable (R S : Type u) [CommRing R] [CommRing S] [Algebra R S]
  (M : ModuleCat.{u} S)

local notation "U" => S ⊗[R] S

/-- On pure tensors the first iterated model moves the old coefficient onto its module. -/
theorem firstTripleModel_tmul (u : U) (c : S) (p : ModuleModels.firstPullback R S M) :
    (TripleExtension.firstTripleModel R S M).hom ((u ⊗ₜ[R] c) ⊗ₜ[U,TripleGluing.pair12 R S] p) =
      c ⊗ₜ[R] ModuleModels.firstModel R S M (u • p) := by
  rfl

/-- The same formula holds for the second iterated model. -/
theorem secondTripleModel_tmul (u : U) (c : S) (p : ModuleModels.secondPullback R S M) :
    (TripleExtension.secondTripleModel R S M).hom ((u ⊗ₜ[R] c) ⊗ₜ[U,TripleGluing.pair12 R S] p) =
      c ⊗ₜ[R] ModuleModels.secondModel R S M (u • p) := by
  rfl

@[simp]
theorem firstFlatModel_tmul (a b c : S) (m : M) :
    (TripleGluing.firstFlatModel R S M).hom (((a ⊗ₜ[R] b) ⊗ₜ[R] c) ⊗ₜ[S,TripleGluing.slot1 R S] m) =
      c ⊗ₜ[R] (b ⊗ₜ[R] (a •
        (show (restrictScalars (algebraMap R S)).obj M from m))) := by
  let p : ModuleModels.firstPullback R S M := (1 : U) ⊗ₜ[S,ModuleModels.firstMap R S] m
  have hp : (a ⊗ₜ[R] b) • p = (a ⊗ₜ[R] b) ⊗ₜ[S,ModuleModels.firstMap R S] m :=
    (ExtendScalars.smul_tmul (ModuleModels.firstMap R S) (a ⊗ₜ[R] b) 1 m).trans
      (congrArg (fun x : U => x ⊗ₜ[S,ModuleModels.firstMap R S] m) (mul_one (a ⊗ₜ[R] b)))
  calc
    _ = (TripleExtension.firstTripleModel R S M).hom
        (((a ⊗ₜ[R] b) ⊗ₜ[R] c) ⊗ₜ[U,TripleGluing.pair12 R S] p) :=
      congrArg (TripleExtension.firstTripleModel R S M).hom
        (ExtensionComposition.composition_hom_tmul (ModuleModels.firstMap R S) (TripleGluing.pair12 R S) M
          ((a ⊗ₜ[R] b) ⊗ₜ[R] c) m)
    _ = c ⊗ₜ[R] ModuleModels.firstModel R S M ((a ⊗ₜ[R] b) • p) :=
      firstTripleModel_tmul R S M (a ⊗ₜ[R] b) c p
    _ = c ⊗ₜ[R] ModuleModels.firstModel R S M ((a ⊗ₜ[R] b) ⊗ₜ[S,ModuleModels.firstMap R S] m) :=
      congrArg (fun z : ModuleModels.firstPullback R S M => c ⊗ₜ[R] ModuleModels.firstModel R S M z) hp
    _ = _ := congrArg (fun z : S ⊗[R] (restrictScalars (algebraMap R S)).obj M =>
      c ⊗ₜ[R] z) (ModuleModels.firstModel_tmul R S M a b m)

@[simp]
theorem secondFlatModel_tmul (a b c : S) (m : M) :
    (TripleGluing.secondFlatModel R S M).hom (((a ⊗ₜ[R] b) ⊗ₜ[R] c) ⊗ₜ[S,TripleGluing.slot2 R S] m) =
      c ⊗ₜ[R] (a ⊗ₜ[R] (b •
        (show (restrictScalars (algebraMap R S)).obj M from m))) := by
  let p : ModuleModels.secondPullback R S M := (1 : U) ⊗ₜ[S,ModuleModels.secondMap R S] m
  have hp : (a ⊗ₜ[R] b) • p = (a ⊗ₜ[R] b) ⊗ₜ[S,ModuleModels.secondMap R S] m :=
    (ExtendScalars.smul_tmul (ModuleModels.secondMap R S) (a ⊗ₜ[R] b) 1 m).trans
      (congrArg (fun x : U => x ⊗ₜ[S,ModuleModels.secondMap R S] m) (mul_one (a ⊗ₜ[R] b)))
  calc
    _ = (TripleExtension.secondTripleModel R S M).hom
        (((a ⊗ₜ[R] b) ⊗ₜ[R] c) ⊗ₜ[U,TripleGluing.pair12 R S] p) :=
      congrArg (TripleExtension.secondTripleModel R S M).hom
        (ExtensionComposition.composition_hom_tmul (ModuleModels.secondMap R S) (TripleGluing.pair12 R S) M
          ((a ⊗ₜ[R] b) ⊗ₜ[R] c) m)
    _ = c ⊗ₜ[R] ModuleModels.secondModel R S M ((a ⊗ₜ[R] b) • p) :=
      secondTripleModel_tmul R S M (a ⊗ₜ[R] b) c p
    _ = c ⊗ₜ[R] ModuleModels.secondModel R S M ((a ⊗ₜ[R] b) ⊗ₜ[S,ModuleModels.secondMap R S] m) :=
      congrArg (fun z : ModuleModels.secondPullback R S M => c ⊗ₜ[R] ModuleModels.secondModel R S M z) hp
    _ = _ := congrArg (fun z : S ⊗[R] (restrictScalars (algebraMap R S)).obj M =>
      c ⊗ₜ[R] z) (ModuleModels.secondModel_tmul R S M a b m)

end

end OAI.AlgebraicGeometry.Picard.PoincareBundle.Cech.FlatCoordinates

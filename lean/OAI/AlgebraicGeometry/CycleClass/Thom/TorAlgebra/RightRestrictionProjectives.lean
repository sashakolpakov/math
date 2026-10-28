import OAI.AlgebraicGeometry.CycleClass.Thom.TorAlgebra.RestrictionProjectives
import OAI.AlgebraicGeometry.CycleClass.Thom.Tensor.ProductRightAlgebra
import Mathlib.LinearAlgebra.Basis.VectorSpace

/-! # Right Restriction Projectives -/

namespace OAI.AlgebraicGeometry.CycleClass.Thom.TorAlgebra.RightRestrictionProjectives

noncomputable section

/-! Restriction to the right factor of a tensor algebra over a field
preserves projective modules. The free algebra is identified with
the scalar extension of the left factor by the actual tensor swap. -/

open _root_.CategoryTheory
open scoped TensorProduct

open OAI.AlgebraicGeometry.CycleClass.Thom.Tensor.ProductRightAlgebra.Constructions

universe u
variable (k R S : Type u) [Field k] [CommRing R] [CommRing S] [Algebra k R] [Algebra k S]

attribute [local instance] Algebra.TensorProduct.rightAlgebra

def rightRestriction : ModuleCat.{u} (R ⊗[k] S) ⥤ ModuleCat.{u} S :=
  ModuleCat.restrictScalars (algebraMap S (R ⊗[k] S))

def freeModelEquiv :
    (rightRestriction k R S).obj (ModuleCat.of (R ⊗[k] S) (R ⊗[k] S)) ≃ₗ[S] R ⊗[k] S where
  __ := AddEquiv.refl (R ⊗[k] S)
  map_smul' s a := (Algebra.smul_def s (show R ⊗[k] S from a)).symm

def freeTensorEquiv :
    (rightRestriction k R S).obj (ModuleCat.of (R ⊗[k] S) (R ⊗[k] S)) ≃ₗ[S] S ⊗[k] R :=
  (freeModelEquiv k R S).trans (Tensor.ProductRightAlgebra.Constructions.rightSwap k R S).toLinearEquiv

instance free_projective :
    Projective ((rightRestriction k R S).obj (ModuleCat.of (R ⊗[k] S) (R ⊗[k] S))) := by
  let : Module.Projective k R := inferInstance
  let : Module.Projective S (S ⊗[k] R) := inferInstance
  let : Module.Projective S ((rightRestriction k R S).obj (ModuleCat.of (R ⊗[k] S) (R ⊗[k] S))) :=
    Module.Projective.of_equiv' (freeTensorEquiv k R S).symm
  infer_instance

instance rightRestriction_preservesProjectiveObjects :
    (rightRestriction k R S).PreservesProjectiveObjects := by
  let : Projective ((ModuleCat.restrictScalars (algebraMap S (R ⊗[k] S))).obj
      (ModuleCat.of (R ⊗[k] S) (R ⊗[k] S))) := free_projective k R S
  exact RestrictionProjectives.restriction_preservesProjectiveObjects S (R ⊗[k] S)

end

end OAI.AlgebraicGeometry.CycleClass.Thom.TorAlgebra.RightRestrictionProjectives

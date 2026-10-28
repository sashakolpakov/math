import OAI.AlgebraicGeometry.CycleClass.Thom.TorAlgebra.TensorOverBase
import Mathlib.LinearAlgebra.DirectSum.Finsupp
import Mathlib.Algebra.Category.ModuleCat.Projective
import Mathlib.CategoryTheory.Preadditive.Projective.Preserves

/-! # Tensor Over Base Projectives -/

namespace OAI.AlgebraicGeometry.CycleClass.Thom.TorAlgebra.TensorOverBaseProjectives

noncomputable section

/-! Tensoring over one base and restricting through a second algebra
map preserves projectives whenever it sends the rank-one free algebra
module to a projective module. The proof uses actual free-module splittings. -/

open _root_.CategoryTheory
open scoped TensorProduct Classical

open OAI.AlgebraicGeometry.CycleClass.Thom.TorAlgebra.TensorOverBase

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u
variable (S A L : Type u) [CommRing S] [CommRing A] [CommRing L]
  [Algebra S A] [Algebra L A] (N : ModuleCat.{u} S)

attribute [local instance] TensorOverBase.moduleCarrier
  TensorOverBase.scalarTowerCarrier

def tensorRestriction : ModuleCat.{u} A ⥤ ModuleCat.{u} L :=
  TensorOverBase.tensorOverBase S A N ⋙ ModuleCat.restrictScalars (algebraMap L A)

theorem freeScalarModule_eq (ι : Type u) :
    Module.compHom (ι →₀ A) (algebraMap S A) = (inferInstance : Module S (ι →₀ A)) := by
  ext s f i
  change (algebraMap S A s) * f i = s • f i
  exact (Algebra.smul_def s (f i)).symm

def freeTensorCoordinates (M : ModuleCat.{u} A) (ι : Type u) :
    (TensorOverBase.tensorOverBase S A N).obj (ModuleCat.of A (ι →₀ M)) ≃ₗ[A]
      (ι →₀ (TensorOverBase.tensorOverBase S A N).obj M) := by
  let i : (ModuleCat.of A (ι →₀ M)) ≃ₗ[A] (ι →₀ M) := LinearEquiv.refl A _
  exact (TensorProduct.AlgebraTensorModule.congr i (LinearEquiv.refl S N)).trans
    (TensorProduct.finsuppLeft S A M N ι)

def freeComponent (ι : Type u) :
    (tensorRestriction S A L N).obj (ModuleCat.of A (ι →₀ A)) ≃ₗ[L]
      (ι →₀ (tensorRestriction S A L N).obj (ModuleCat.of A A)) where
  __ := (freeTensorCoordinates S A N (ModuleCat.of A A) ι).toAddEquiv
  map_smul' l x := (freeTensorCoordinates S A N (ModuleCat.of A A) ι).map_smul (algebraMap L A l) x

variable [Projective ((tensorRestriction S A L N).obj (ModuleCat.of A A))]

theorem free_projective (ι : Type u) :
    Projective ((tensorRestriction S A L N).obj (ModuleCat.of A (ι →₀ A))) := by
  let : Module.Projective L ((tensorRestriction S A L N).obj (ModuleCat.of A A)) := inferInstance
  let : Module.Projective L (ι →₀ (tensorRestriction S A L N).obj (ModuleCat.of A A)) :=
    Module.Projective.of_equiv' (finsuppLEquivDirectSum L _ ι).symm
  let : Module.Projective L ((tensorRestriction S A L N).obj (ModuleCat.of A (ι →₀ A))) :=
    Module.Projective.of_equiv' (freeComponent S A L N ι).symm
  infer_instance

instance tensorRestriction_preservesProjectiveObjects :
    (tensorRestriction S A L N).PreservesProjectiveObjects where
  projective_obj {M} hM := by
    let : Projective M := hM
    let : Module.Projective A M := inferInstance
    obtain ⟨s, hs⟩ := (inferInstance : Module.Projective A M)
    let i : M ⟶ ModuleCat.of A (M →₀ A) := ModuleCat.ofHom s
    let j : ModuleCat.of A (M →₀ A) ⟶ M := ModuleCat.ofHom (Finsupp.linearCombination A id)
    have hij : i ≫ j = 𝟙 M := ModuleCat.hom_ext (LinearMap.ext hs)
    let : Projective ((tensorRestriction S A L N).obj (ModuleCat.of A (M →₀ A))) :=
      free_projective S A L N M
    let : Module.Projective L ((tensorRestriction S A L N).obj (ModuleCat.of A (M →₀ A))) := inferInstance
    have hf := congrArg (tensorRestriction S A L N).map hij
    rw [(tensorRestriction S A L N).map_comp, (tensorRestriction S A L N).map_id] at hf
    let : Module.Projective L ((tensorRestriction S A L N).obj M) := Module.Projective.of_split
      ((tensorRestriction S A L N).map i).hom ((tensorRestriction S A L N).map j).hom
      (congrArg ModuleCat.Hom.hom hf)
    infer_instance

end

end OAI.AlgebraicGeometry.CycleClass.Thom.TorAlgebra.TensorOverBaseProjectives

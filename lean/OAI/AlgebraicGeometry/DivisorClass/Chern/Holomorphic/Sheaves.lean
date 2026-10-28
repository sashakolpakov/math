import OAI.AlgebraicGeometry.DivisorClass.Chern.Holomorphic.Exponential
import Mathlib.Algebra.Category.Grp.Adjunctions
import Mathlib.Algebra.Category.Grp.EquivalenceGroupAddGroup
import Mathlib.CategoryTheory.Sites.Whiskering
import Mathlib.Algebra.Category.Ring.Limits
import Mathlib.Algebra.Category.Ring.Adjunctions

/-! # Sheaves -/

namespace OAI.AlgebraicGeometry.DivisorClass.Chern.Holomorphic.Sheaves

noncomputable section

/-! The genuine holomorphic function and unit sheaves, with their actual exponential map. -/

open _root_.CategoryTheory _root_.TopologicalSpace Opposite
open scoped _root_.Manifold ContDiff

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

variable (E : Type) [NormedAddCommGroup E] [NormedSpace ℂ E]
variable (M : Type) [TopologicalSpace M] [ChartedSpace E M]

abbrev holomorphicFunctionSheaf : TopCat.Sheaf AddCommGrpCat (TopCat.of M) :=
  smoothSheafAddCommGroup 𝓘(ℂ, E) 𝓘(ℂ) M ℂ

abbrev holomorphicRingSheaf : TopCat.Sheaf CommRingCat (TopCat.of M) :=
  smoothSheafCommRing 𝓘(ℂ, E) 𝓘(ℂ) M ℂ

def holomorphicUnitsSheaf : TopCat.Sheaf AddCommGrpCat (TopCat.of M) :=
  letI : CommGrpCat.toAddCommGrp.IsEquivalence :=
    inferInstanceAs commGroupAddCommGroupEquivalence.functor.IsEquivalence
  let J := Opens.grothendieckTopology (TopCat.of M)
  let R := (sheafCompose J (forget₂ CommRingCat CommMonCat)).obj (holomorphicRingSheaf E M)
  let U := (sheafCompose J CommMonCat.units).obj R
  (sheafCompose J CommGrpCat.toAddCommGrp).obj U

def holomorphicExponentialSheafMap : holomorphicFunctionSheaf E M ⟶ holomorphicUnitsSheaf E M :=
  ObjectProperty.homMk {
    app U := AddCommGrpCat.ofHom (Exponential.holomorphicExponential (E := E) (M := U.unop))
    naturality := by
      intro U V i
      apply AddCommGrpCat.hom_ext
      ext g
      apply Units.ext
      apply ContMDiffMap.ext
      intro x
      rfl }

theorem holomorphicExponentialSheafMap_apply (U : Opens M)
    (g : Exponential.HolomorphicFunction (E := E) (M := U)) :
    (holomorphicExponentialSheafMap E M).hom.app (op U) g = Additive.ofMul (Exponential.holomorphicExpUnit g) := rfl

end

end OAI.AlgebraicGeometry.DivisorClass.Chern.Holomorphic.Sheaves

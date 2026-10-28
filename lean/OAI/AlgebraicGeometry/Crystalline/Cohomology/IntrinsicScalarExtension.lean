import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings

/-! # Intrinsic Scalar Extension -/

namespace OAI.AlgebraicGeometry.Crystalline.Cohomology.IntrinsicScalarExtension

noncomputable section

/-! # Additive scalar extension using the specified algebra action -/

open _root_.CategoryTheory
open scoped TensorProduct

universe u

variable (R S : Type u) [CommRing R] [CommRing S] [Algebra R S]

def functor : ModuleCat.{u} R ⥤ ModuleCat.{u} S where
  obj M := ModuleCat.of S (S ⊗[R] M)
  map f := ModuleCat.ofHom (f.hom.baseChange S)
  map_id _ := ModuleCat.hom_ext LinearMap.baseChange_id
  map_comp f g := ModuleCat.hom_ext (LinearMap.baseChange_comp (A := S) f.hom g.hom)

instance additive : (functor R S).Additive where
  map_add {_M _N} f g := ModuleCat.hom_ext (LinearMap.baseChange_add (A := S) f.hom g.hom)

end

end OAI.AlgebraicGeometry.Crystalline.Cohomology.IntrinsicScalarExtension

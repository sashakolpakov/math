import Mathlib.Algebra.Category.ModuleCat.ChangeOfRingsExact
import Mathlib.RingTheory.Flat.Basic

/-! # Flat Scalar Extension -/

namespace OAI.AlgebraicGeometry.Crystalline.Cohomology.Large.FlatScalarExtension.LargeFlatScalarExtension

noncomputable section

/-!
# Flat scalar extension in the original cohomology universes

The functor uses the given algebra action on the coefficient ring.
Flatness proves exactness for the original large module category.
-/

open _root_.CategoryTheory _root_.CategoryTheory.Limits
open scoped TensorProduct

universe u

variable (R S : Type u) [CommRing R] [CommRing S] [Algebra R S]

def functor : ModuleCat.{u + 2} R ⥤ ModuleCat.{u + 2} S where
  obj M := ModuleCat.of S (S ⊗[R] M)
  map f := ModuleCat.ofHom (f.hom.baseChange S)
  map_id _ := ModuleCat.hom_ext (LinearMap.baseChange_id)
  map_comp f g := ModuleCat.hom_ext (LinearMap.baseChange_comp (A := S) f.hom g.hom)

instance additive : (functor R S).Additive where
  map_add {_M _N} f g := ModuleCat.hom_ext (LinearMap.baseChange_add (A := S) f.hom g.hom)

variable [Module.Flat R S]

theorem map_exact (C : ShortComplex (ModuleCat.{u + 2} R)) (hC : C.Exact) :
    (C.map (functor R S)).Exact := by
  rw [ShortComplex.ShortExact.moduleCat_exact_iff_function_exact] at hC ⊢
  change Function.Exact (C.f.hom.baseChange S) (C.g.hom.baseChange S)
  exact Module.Flat.lTensor_exact S hC

instance finiteLimits : PreservesFiniteLimits (functor R S) := by
  have h : PreservesFiniteLimits (functor R S) ∧ PreservesFiniteColimits (functor R S) :=
    ((Functor.exact_tfae (functor R S)).out 2 4).mp (map_exact R S)
  exact h.1

instance finiteColimits : PreservesFiniteColimits (functor R S) := by
  have h : PreservesFiniteLimits (functor R S) ∧ PreservesFiniteColimits (functor R S) :=
    ((Functor.exact_tfae (functor R S)).out 2 4).mp (map_exact R S)
  exact h.2

instance preservesHomology : (functor R S).PreservesHomology := Functor.preservesHomologyOfExact _

end

end OAI.AlgebraicGeometry.Crystalline.Cohomology.Large.FlatScalarExtension.LargeFlatScalarExtension

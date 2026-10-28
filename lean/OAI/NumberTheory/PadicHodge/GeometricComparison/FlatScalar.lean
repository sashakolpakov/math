import Mathlib.Algebra.Category.ModuleCat.ChangeOfRingsExact
import Mathlib.RingTheory.Flat.Basic

/-! # Flat Scalar -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.FlatScalar.FlatScalarExtension

noncomputable section

/-! The scalar-extension functor uses the given algebra structure and preserves homology for flat coefficients. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits
open scoped TensorProduct

universe u v

variable (R S : Type u) [CommRing R] [CommRing S] [Algebra R S]

def moduleFunctor : ModuleCat.{max u v} R ⥤ ModuleCat.{max u v} S where
  obj M := ModuleCat.of S (S ⊗[R] M)
  map f := ModuleCat.ofHom (f.hom.baseChange S)
  map_id _ := ModuleCat.hom_ext LinearMap.baseChange_id
  map_comp f g := ModuleCat.hom_ext (LinearMap.baseChange_comp (A := S) f.hom g.hom)

instance additive : (moduleFunctor.{u, v} R S).Additive where
  map_add {_M _N} f g := ModuleCat.hom_ext (LinearMap.baseChange_add (A := S) f.hom g.hom)

variable [Module.Flat R S]

theorem map_exact (C : ShortComplex (ModuleCat.{max u v} R)) (hC : C.Exact) :
    (C.map (moduleFunctor R S)).Exact := by
  rw [ShortComplex.ShortExact.moduleCat_exact_iff_function_exact] at hC ⊢
  change Function.Exact (C.f.hom.baseChange S) (C.g.hom.baseChange S)
  exact Module.Flat.lTensor_exact S hC

instance finiteLimits : PreservesFiniteLimits (moduleFunctor.{u, v} R S) := by
  have h : PreservesFiniteLimits (moduleFunctor.{u, v} R S) ∧
      PreservesFiniteColimits (moduleFunctor.{u, v} R S) :=
    ((Functor.exact_tfae (moduleFunctor.{u, v} R S)).out 2 4).mp (map_exact R S)
  exact h.1

instance finiteColimits : PreservesFiniteColimits (moduleFunctor.{u, v} R S) := by
  have h : PreservesFiniteLimits (moduleFunctor.{u, v} R S) ∧
      PreservesFiniteColimits (moduleFunctor.{u, v} R S) :=
    ((Functor.exact_tfae (moduleFunctor.{u, v} R S)).out 2 4).mp (map_exact R S)
  exact h.2

instance preservesHomology : (moduleFunctor.{u, v} R S).PreservesHomology :=
  Functor.preservesHomologyOfExact _

end

end OAI.NumberTheory.PadicHodge.GeometricComparison.FlatScalar.FlatScalarExtension

import OAI.NumberTheory.PadicHodge.IntegralComparison.InjectiveCoefficientDuality
import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
import Mathlib.Algebra.Homology.ShortComplex.ExactFunctor

/-! # Exact Module Dual Functor -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.ExactModuleDualFunctor

noncomputable section

/-! The ordinary coefficient dual as an exact contravariant functor when
the coefficient ring is injective over itself. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits Opposite

universe u

variable (R : Type u) [CommRing R]

def functor : (ModuleCat.{u} R)ᵒᵖ ⥤ ModuleCat.{u} R where
  obj M := ModuleCat.of R (Module.Dual R M.unop)
  map f := ModuleCat.ofHom f.unop.hom.dualMap
  map_id M := by
    ext φ x
    rfl
  map_comp f g := by
    ext φ x
    rfl

instance : (functor R).Additive where
  map_add := by
    intro X Y f g
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro φ
    apply LinearMap.ext
    intro x
    exact φ.map_add _ _

theorem map_exact [Module.Injective R R]
    (S : ShortComplex ((ModuleCat.{u} R)ᵒᵖ)) (h : S.Exact) :
    (S.map (functor R)).Exact := by
  apply (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).mpr
  exact InjectiveCoefficientDuality.dual_exact S.g.unop.hom S.f.unop.hom
    ((ShortComplex.ShortExact.moduleCat_exact_iff_function_exact S.unop).mp h.unop)

instance [Module.Injective R R] : (functor R).PreservesHomology :=
  Functor.preservesHomology_of_map_exact (functor R) (map_exact R)

instance [Module.Injective R R] : PreservesFiniteLimits (functor R) :=
  Functor.preservesFiniteLimits_of_preservesHomology (functor R)

instance [Module.Injective R R] : PreservesFiniteColimits (functor R) :=
  Functor.preservesFiniteColimits_of_preservesHomology (functor R)

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.ExactModuleDualFunctor

import OAI.NumberTheory.PadicHodge.PeriodInvariants.ConstantSheafCoherence
import Mathlib.Algebra.Homology.DerivedCategory.Ext.Linear

/-! # Degree Zero Sections -/

namespace OAI.NumberTheory.PadicHodge.PeriodInvariants.DegreeZeroSections

noncomputable section

/-!
# Actual degree-zero Ext from a constant rank-one sheaf

The degree-zero Ext equivalence, the constant-sheaf adjunction, and
evaluation at one identify degree-zero cohomology with sections over
the terminal object. All identifications preserve the coefficient action.
-/

open _root_.CategoryTheory _root_.CategoryTheory.Limits Opposite

universe u v w t

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
variable (R : Type w) [CommRing R] [HasSheafify J (ModuleCat.{w} R)]
variable {T : C} (hT : IsTerminal T)

def homSectionsEquiv (F : Sheaf J (ModuleCat.{w} R)) :
    ((constantSheaf J (ModuleCat.{w} R)).obj (ModuleCat.of R R) ⟶ F) ≃ F.obj.obj (op T) :=
  ((constantSheafAdj J (ModuleCat.{w} R) hT).homEquiv (ModuleCat.of R R) F).trans
    ((ModuleCat.homLinearEquiv (R := R) (S := R)).toEquiv.trans
      (LinearMap.ringLmapEquivSelf R R _).toEquiv)

theorem homSectionsEquiv_apply (F : Sheaf J (ModuleCat.{w} R))
    (f : (constantSheaf J (ModuleCat.{w} R)).obj (ModuleCat.of R R) ⟶ F) :
    homSectionsEquiv J R hT F f =
      ((constantSheafAdj J (ModuleCat.{w} R) hT).homEquiv (ModuleCat.of R R) F f) 1 := rfl

def homSectionsLinearEquiv (F : Sheaf J (ModuleCat.{w} R)) :
    ((constantSheaf J (ModuleCat.{w} R)).obj (ModuleCat.of R R) ⟶ F) ≃ₗ[R] F.obj.obj (op T) where
  toEquiv := homSectionsEquiv J R hT F
  map_add' f g := by
    change homSectionsEquiv J R hT F (f + g) = homSectionsEquiv J R hT F f + homSectionsEquiv J R hT F g
    simp only [homSectionsEquiv_apply, Adjunction.homEquiv_unit]
    rfl
  map_smul' c f := by
    change homSectionsEquiv J R hT F (c • f) = c • homSectionsEquiv J R hT F f
    simp only [homSectionsEquiv_apply, Adjunction.homEquiv_unit]
    rfl

variable [HasExt.{t} (Sheaf J (ModuleCat.{w} R))]

def degreeZeroEquiv (F : Sheaf J (ModuleCat.{w} R)) :
    Abelian.Ext.{t} ((constantSheaf J (ModuleCat.{w} R)).obj (ModuleCat.of R R)) F 0 ≃ₗ[R]
      F.obj.obj (op T) :=
  (Abelian.Ext.linearEquiv₀ (R := R)).trans (homSectionsLinearEquiv J R hT F)

end

end OAI.NumberTheory.PadicHodge.PeriodInvariants.DegreeZeroSections

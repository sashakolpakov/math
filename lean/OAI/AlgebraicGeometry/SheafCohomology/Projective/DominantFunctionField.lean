import Mathlib.AlgebraicGeometry.FunctionField
import Mathlib.AlgebraicGeometry.Morphisms.UnderlyingMap

/-! # Dominant Function Field -/

namespace OAI.AlgebraicGeometry.SheafCohomology.Projective.DominantFunctionField.Dimension

noncomputable section

/-! A dominant map of integral schemes induces the actual inclusion of function fields. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace

universe u

variable {X Y : Scheme.{u}} [IsIntegral X] [IsIntegral Y]

theorem dominant_genericPoint (f : X ⟶ Y) [IsDominant f] :
    f (genericPoint X) = genericPoint Y := by
  apply ((genericPoint_spec Y).eq _).symm
  convert! (genericPoint_spec X).image f.continuous using 1
  rw [Set.image_univ, f.denseRange.closure_eq]

def dominantFunctionFieldMap (f : X ⟶ Y) [IsDominant f] :
    Y.functionField ⟶ X.functionField :=
  eqToHom (congrArg (fun y => Y.presheaf.stalk y) (dominant_genericPoint f).symm) ≫
    f.stalkMap (genericPoint X)

@[instance_reducible]
def dominantFunctionFieldAlgebra (f : X ⟶ Y) [IsDominant f] :
    Algebra Y.functionField X.functionField := (dominantFunctionFieldMap f).hom.toAlgebra

omit [IsIntegral Y] in
theorem scheme_germ_point_cast (U : Y.Opens) {x y : Y} (h : x = y) (hx : x ∈ U) :
    Y.presheaf.germ U x hx ≫ eqToHom (congrArg (fun z => Y.presheaf.stalk z) h) =
      Y.presheaf.germ U y (h ▸ hx) := by
  subst y
  simp

theorem dominantFunctionFieldMap_germ (f : X ⟶ Y) [IsDominant f]
    (U : Y.Opens) [Nonempty U] [Nonempty (f ⁻¹ᵁ U)] :
    Y.germToFunctionField U ≫ dominantFunctionFieldMap f =
      f.app U ≫ X.germToFunctionField (f ⁻¹ᵁ U) := by
  dsimp only [dominantFunctionFieldMap, Scheme.germToFunctionField]
  rw [← Category.assoc, scheme_germ_point_cast U (dominant_genericPoint f).symm, Scheme.Hom.germ_stalkMap]

end

end OAI.AlgebraicGeometry.SheafCohomology.Projective.DominantFunctionField.Dimension

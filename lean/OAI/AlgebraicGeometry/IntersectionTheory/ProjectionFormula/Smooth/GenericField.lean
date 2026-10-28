import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Smooth.Order
import Mathlib.AlgebraicGeometry.Morphisms.UniversallyOpen

/-! # Generic Field -/

namespace OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Smooth.GenericField

noncomputable section

/-! The generic field map of a smooth morphism is the actual generic
stalk map. Divisor points over the generic point contribute zero order. -/

set_option backward.isDefEq.respectTransparency false

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace _root_.Order

universe u

theorem genericPoint_image {X Y : Scheme.{u}} [IsIntegral X] [IsIntegral Y]
    (f : X ⟶ Y) [Smooth f] : f (genericPoint X) = genericPoint Y := by
  apply ((genericPoint_spec Y).eq _).symm
  convert! (genericPoint_spec X).image f.continuous
  symm
  rw [← Set.univ_subset_iff]
  have ho : IsOpen (Set.range f) := by simpa only [Set.image_univ] using f.isOpenMap Set.univ isOpen_univ
  convert! subset_closure_inter_of_isPreirreducible_of_isOpen _ ho _
  · rw [Set.univ_inter, Set.image_univ]
  · exact PreirreducibleSpace.isPreirreducible_univ (X := Y)
  · exact ⟨f (genericPoint X), trivial, Set.mem_range_self _⟩

def fieldMap {X Y : Scheme.{u}} [IsIntegral X] [IsIntegral Y]
    (f : X ⟶ Y) [Smooth f] : Y.functionField ⟶ X.functionField :=
  Cycles.Functoriality.FunctionFields.Construction.genericFieldMap f (genericPoint_image f)

theorem ord_generic_image {X Y : Scheme.{u}} [IsIntegral X] [IsIntegral Y]
    [IsLocallyNoetherian X] (f : X ⟶ Y) [Smooth f]
    (x : X) (hx : coheight x = 1) (hy : f x = genericPoint Y) (g : Y.functionField) :
    X.ord (fieldMap f g) x = 0 := by
  by_cases hg : g = 0
  · subst g
    simp only [map_zero, Scheme.ord_zero, Pi.zero_apply]
  let R := Y.presheaf.stalk (f x)
  let S := X.presheaf.stalk x
  have hf : IsField R := by
    change IsField (Y.presheaf.stalk (f x))
    rw [hy]
    exact Field.toIsField Y.functionField
  obtain ⟨a, ha⟩ := (IsFractionRing.surjective_iff_isField (R := R) (K := Y.functionField)).mpr hf g
  have ha0 : a ≠ 0 := by intro h; apply hg; rw [← ha, h, map_zero]
  have hau : IsUnit a := by
    let := hf.toField
    exact isUnit_iff_ne_zero.mpr ha0
  have he : fieldMap f g = algebraMap S X.functionField (f.stalkMap x a) := by
    rw [← ha]
    exact Divisor.DivisorRestriction.genericFieldMap_stalk f (genericPoint_image f) x a
  let : Ring.KrullDimLE 1 S := krullDimLE_of_coheight_le hx.le
  rw [he, Scheme.ord_eq_ordHom_of_coheight_eq_one hx]
  change WithZero.log (Ring.ordFrac S (algebraMap S X.functionField (f.stalkMap x a))) = 0
  rw [Ring.ordFrac_of_isUnit (hau.map (f.stalkMap x).hom)]
  rfl

end

end OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Smooth.GenericField

import OAI.AlgebraicGeometry.Divisors.LineBundles.Support.Integrality
import OAI.AlgebraicGeometry.Cycles.Functoriality.FunctionFields

/-! # Function Field -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.Deformation.FunctionField.BundleCycles

noncomputable section

/-!
# LineBundleCycles: rational functions on the actual support deformation

The constructed projection is surjective, hence dominant. Its generic
stalk map therefore embeds the original support's function field in the
deformation's function field. On every nonempty open, this is exactly
pullback of the regular-function representative by the structural map.
-/

open _root_.AlgebraicGeometry _root_.CategoryTheory _root_.TopologicalSpace

universe u

/-- A surjective morphism of integral schemes sends the generic point to the generic point. -/
theorem genericPoint_eq_of_surjective {A B : Scheme.{u}} [IsIntegral A] [IsIntegral B]
    (i : A ⟶ B) (hi : Function.Surjective i) : i (genericPoint A) = genericPoint B := by
  apply IsGenericPoint.eq _ (genericPoint_spec B)
  have h := (genericPoint_spec A).image i.continuous
  simp only [Set.image_univ, hi.range_eq, closure_univ] at h
  exact h

/-- Generic-stalk pullback agrees with pullback on every nonempty open. -/
theorem genericFieldMap_germOn {A B : Scheme.{u}} [IsIntegral A] [IsIntegral B]
    (i : A ⟶ B) (hη : i (genericPoint A) = genericPoint B)
    (U : B.Opens) [Nonempty U] [Nonempty (i ⁻¹ᵁ U)] :
    B.germToFunctionField U ≫ Cycles.Functoriality.FunctionFields.Construction.genericFieldMap i hη =
      i.app U ≫ A.germToFunctionField (i ⁻¹ᵁ U) := by
  simp only [Cycles.Functoriality.FunctionFields.Construction.genericFieldMap, TopCat.Presheaf.stalkCongr_hom, ← Category.assoc]
  have hx : genericPoint A ∈ i ⁻¹ᵁ U :=
    (genericPoint_spec A).mem_open_set_iff (i ⁻¹ᵁ U).isOpen |>.mpr
      (by simpa using (show Nonempty (i ⁻¹ᵁ U) from inferInstance))
  have h := B.presheaf.germ_stalkSpecializes
    (show genericPoint B ∈ U from hη ▸ hx) (Inseparable.of_eq hη).specializes
  exact (congrArg
    (fun k : Γ(B, U) ⟶ B.presheaf.stalk (i (genericPoint A)) => k ≫ i.stalkMap (genericPoint A)) h).trans
    (i.germ_stalkMap U (genericPoint A) hx)

variable {X : Scheme.{u}} (I P : X.IdealSheafData) [IsIntegral P.subscheme]

theorem globalSupportDeformationToSupport_genericPoint :
    Support.Projection.BundleCycles.globalSupportDeformationToSupport I P (genericPoint (Global.SupportDeformation.BundleCycles.globalSupportDeformation I P)) =
      genericPoint P.subscheme :=
  genericPoint_eq_of_surjective (Support.Projection.BundleCycles.globalSupportDeformationToSupport I P)
    (Support.Projection.BundleCycles.globalSupportDeformationToSupport_surjective I P)

/-- The actual pullback embedding of support rational functions. -/
def globalSupportFunctionFieldMap :
    P.subscheme.functionField ⟶ (Global.SupportDeformation.BundleCycles.globalSupportDeformation I P).functionField :=
  Cycles.Functoriality.FunctionFields.Construction.genericFieldMap (Support.Projection.BundleCycles.globalSupportDeformationToSupport I P)
    (globalSupportDeformationToSupport_genericPoint I P)

theorem globalSupportFunctionFieldMap_injective : Function.Injective (globalSupportFunctionFieldMap I P) :=
  (globalSupportFunctionFieldMap I P).hom.injective

theorem globalSupportFunctionFieldMap_ne_zero (g : P.subscheme.functionField) (hg : g ≠ 0) :
    globalSupportFunctionFieldMap I P g ≠ 0 := by
  intro h
  exact hg ((globalSupportFunctionFieldMap_injective I P)
    (h.trans (map_zero (globalSupportFunctionFieldMap I P).hom).symm))

/-- The regular representatives pull back by the actual scheme morphism on every open. -/
theorem globalSupportFunctionFieldMap_germOn (U : P.subscheme.Opens)
    [Nonempty U] [Nonempty (Support.Projection.BundleCycles.globalSupportDeformationToSupport I P ⁻¹ᵁ U)] :
    P.subscheme.germToFunctionField U ≫ globalSupportFunctionFieldMap I P =
      (Support.Projection.BundleCycles.globalSupportDeformationToSupport I P).app U ≫
        (Global.SupportDeformation.BundleCycles.globalSupportDeformation I P).germToFunctionField
          (Support.Projection.BundleCycles.globalSupportDeformationToSupport I P ⁻¹ᵁ U) :=
  genericFieldMap_germOn (Support.Projection.BundleCycles.globalSupportDeformationToSupport I P)
    (globalSupportDeformationToSupport_genericPoint I P) U

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.Deformation.FunctionField.BundleCycles

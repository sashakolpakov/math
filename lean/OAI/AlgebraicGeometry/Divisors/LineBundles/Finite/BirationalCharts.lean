import OAI.AlgebraicGeometry.Divisors.LineBundles.Finite.BirationalAlgebra

/-! # Birational Charts -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.Finite.BirationalCharts.BundleCycles

noncomputable section

/-!
# LineBundleCycles: a finite birational morphism is an isomorphism over a normal affine chart
-/

open _root_.AlgebraicGeometry _root_.CategoryTheory

universe u
variable {X Y : Scheme.{u}} [IsIntegral X] [IsIntegral Y]
    (f : X ⟶ Y) [IsFinite f] (hη : f (genericPoint X) = genericPoint Y)
    [IsIso (Cycles.Functoriality.FunctionFields.Construction.genericFieldMap f hη)]

include hη

theorem finiteBirational_app_isIso (U : Y.Opens) (hU : IsAffineOpen U)
    [Nonempty U] [IsIntegrallyClosed Γ(Y, U)] : IsIso (f.app U) := by
  let : Nonempty (f ⁻¹ᵁ U) := ⟨⟨genericPoint X, by
    change f (genericPoint X) ∈ U
    rw [hη]
    exact ((genericPoint_spec Y).mem_open_set_iff U.isOpen).mpr
      (by simpa using (show Nonempty U from inferInstance))⟩⟩
  let A := Γ(Y, U)
  let B := Γ(X, f ⁻¹ᵁ U)
  let : Algebra A B := (f.app U).hom.toAlgebra
  let : Module.Finite A B := (IsFinite.finite_app f U hU)
  let := functionField_isFractionRing_of_isAffineOpen Y U hU
  let e := asIso (Cycles.Functoriality.FunctionFields.Construction.genericFieldMap f hη)
  let j : B →ₐ[A] Y.functionField :=
    { toRingHom := e.inv.hom.comp (X.germToFunctionField (f ⁻¹ᵁ U)).hom
      commutes' := by
        intro a
        apply e.hom.hom.injective
        have hs := ConcreteCategory.congr_hom (Deformation.FunctionField.BundleCycles.genericFieldMap_germOn f hη U) a
        exact (ConcreteCategory.congr_hom e.inv_hom_id _).trans hs.symm }
  have hj : Function.Injective j :=
    e.inv.hom.injective.comp (X.germToFunctionField_injective (f ⁻¹ᵁ U))
  exact (ConcreteCategory.isIso_iff_bijective (f.app U)).mpr
    (BirationalAlgebra.BundleCycles.finiteSubalgebra_algebraMap_bijective A B Y.functionField j hj)

theorem finiteBirational_isIso_of_normal_cover {ι : Type*}
    (U : ι → Y.affineOpens) (hU : ⨆ i, (U i : Y.Opens) = ⊤)
    [∀ i, Nonempty (U i : Y.Opens)]
    (hNormal : ∀ i, IsIntegrallyClosed Γ(Y, (U i : Y.Opens))) : IsIso f := by
  apply IsZariskiLocalAtTarget.of_iSup_eq_top
    (P := MorphismProperty.isomorphisms Scheme) (fun i => (U i : Y.Opens)) hU
  intro i
  let := hNormal i
  exact (isIso_morphismRestrict_iff_isIso_app f (U i).property).mpr
    (finiteBirational_app_isIso f hη (U i) (U i).property)

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.Finite.BirationalCharts.BundleCycles

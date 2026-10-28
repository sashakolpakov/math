import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Generic.Fields

/-! # Spec Field -/

namespace OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.SpecField

noncomputable section

/-! The function field of a field spectrum, and a criterion identifying
the function field of an integral scheme from an actual generic map. -/

set_option backward.isDefEq.respectTransparency false

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

variable (L : Type u) [Field L]

local instance : Nonempty (⊤ : (Spec (.of L)).Opens) :=
  ⟨⟨genericPoint (Spec (.of L)), trivial⟩⟩

local instance : Algebra L (Spec (.of L)).functionField :=
  (StructureSheaf.toStalk L (genericPoint (Spec (.of L)))).hom.toAlgebra

local instance : IsFractionRing L (Spec (.of L)).functionField :=
  functionField_isFractionRing_of_affine (.of L)

def fieldIso : CommRingCat.of L ≅ (Spec (.of L)).functionField :=
  (IsFractionRing.algEquiv L L (Spec (.of L)).functionField).toRingEquiv.toCommRingCatIso

theorem fieldIso_hom :
    (fieldIso L).hom = StructureSheaf.toStalk L (genericPoint (Spec (.of L))) := by
  ext a
  exact (IsFractionRing.algEquiv L L (Spec (.of L)).functionField).commutes a

theorem fieldIso_germ :
    (Scheme.ΓSpecIso (.of L)).hom ≫ (fieldIso L).hom =
      (Spec (.of L)).germToFunctionField ⊤ := by
  rw [fieldIso_hom]
  change (Scheme.ΓSpecIso (.of L)).hom ≫ (Scheme.ΓSpecIso (.of L)).inv ≫ _ = _
  simp
  rfl

/-- If the pullback from one nonempty chart has fraction field `L`, the
actual generic-stalk map of `Spec L → X` is an isomorphism. -/
theorem genericFieldMap_bijective_of_chart
    {X : Scheme.{u}} [IsIntegral X] (q : Spec (.of L) ⟶ X)
    (hη : q (genericPoint (Spec (.of L))) = genericPoint X)
    (U : X.Opens) [Nonempty U] (hTop : ⊤ ≤ q ⁻¹ᵁ U)
    (A : Type u) [CommRing A] [Algebra A L] [IsFractionRing A L]
    (e : Γ(X, U) ≅ CommRingCat.of A)
    (he : q.appLE U ⊤ hTop ≫ (Scheme.ΓSpecIso (.of L)).hom =
      e.hom ≫ CommRingCat.ofHom (algebraMap A L)) :
    Function.Bijective (Cycles.Functoriality.FunctionFields.Construction.genericFieldMap q hη) := by
  refine ⟨(Cycles.Functoriality.FunctionFields.Construction.genericFieldMap q hη).hom.injective, ?_⟩
  intro z
  obtain ⟨l, rfl⟩ := (fieldIso L).commRingCatIsoToRingEquiv.surjective z
  obtain ⟨a, b, _, rfl⟩ := IsFractionRing.div_surjective A l
  have h (a : A) : Cycles.Functoriality.FunctionFields.Construction.genericFieldMap q hη
      (X.germToFunctionField U (e.inv a)) = (fieldIso L).hom (algebraMap A L a) := by
    have hs := Generic.Fields.genericFieldMap_germ_appLE q hη U ⊤ hTop
    rw [← fieldIso_germ L, ← Category.assoc, he] at hs
    simpa using congrArg (fun t : Γ(X, U) ⟶ (Spec (.of L)).functionField => t (e.inv a)) hs
  refine ⟨X.germToFunctionField U (e.inv a) / X.germToFunctionField U (e.inv b), ?_⟩
  rw [map_div₀, h, h, map_div₀]
  rfl

end

end OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.SpecField

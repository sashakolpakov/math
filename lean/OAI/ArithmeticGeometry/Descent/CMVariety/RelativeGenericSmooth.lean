import OAI.ArithmeticGeometry.Descent.CMVariety.GenericSmoothNeighborhood

/-! # Relative Generic Smooth -/

namespace OAI.ArithmeticGeometry.Descent.CMVariety.RelativeGenericSmooth.Abelian

noncomputable section

/-!
A finite-presentation morphism between integral schemes is smooth at the
generic point when it maps generic point to generic point and the target
function field has characteristic zero. This handles coefficient
extensions over an existing arithmetic parameter.
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry

theorem genericPoint_mem_smoothLocus_of_generic_image
    {X Y : Scheme} [IsIntegral X] [IsIntegral Y] [CharZero Y.functionField]
    (f : X ⟶ Y) [LocallyOfFinitePresentation f]
    (hf : f (genericPoint X) = genericPoint Y) :
    genericPoint X ∈ f.smoothLocus := by
  have := LocallyOfFiniteType.stalkMap f (genericPoint X)
  rw [Scheme.Hom.mem_smoothLocus]
  have hfield : IsField (Y.presheaf.stalk (f (genericPoint X))) := by
    rw [hf]
    exact Field.toIsField Y.functionField
  have : CharZero (Y.presheaf.stalk (f (genericPoint X))) := by
    rw [hf]
    exact inferInstanceAs (CharZero Y.functionField)
  let : Field (Y.presheaf.stalk (f (genericPoint X))) := hfield.toField
  algebraize [(f.stalkMap (genericPoint X)).hom]
  exact Algebra.FormallySmooth.of_perfectField

theorem generic_complex_point_factors_through_relative_smooth_open
    {X Y : Scheme} [IsIntegral X] [IsIntegral Y] [CharZero Y.functionField]
    (f : X ⟶ Y) [LocallyOfFinitePresentation f]
    (hf : f (genericPoint X) = genericPoint Y)
    (p : Spec (CommRingCat.of ℂ) ⟶ X)
    (hp : p (IsLocalRing.closedPoint ℂ) = genericPoint X) :
    ∃ U : X.Opens, IsIntegral U ∧ Smooth (U.ι ≫ f) ∧
      ∃ q : Spec (CommRingCat.of ℂ) ⟶ U, q ≫ U.ι = p := by
  let U := f.smoothLocus
  have hU : genericPoint X ∈ U := genericPoint_mem_smoothLocus_of_generic_image f hf
  let : Nonempty U := ⟨⟨genericPoint X, hU⟩⟩
  have hInt : IsIntegral U := isIntegral_of_isOpenImmersion U.ι
  have hSmooth : Smooth (U.ι ≫ f) := by
    apply Scheme.Hom.smoothLocus_eq_top_iff.mp
    rw [← Scheme.Hom.preimage_smoothLocus_eq]
    apply le_antisymm le_top
    intro x _
    exact x.property
  have hrange : Set.range p ⊆ Set.range U.ι := by
    rintro z ⟨w, rfl⟩
    have hw : w = IsLocalRing.closedPoint ℂ := Subsingleton.elim _ _
    rw [hw, hp]
    exact ⟨⟨genericPoint X, hU⟩, rfl⟩
  exact ⟨U, hInt, hSmooth, IsOpenImmersion.lift U.ι p hrange, IsOpenImmersion.lift_fac _ _ _⟩

end

end OAI.ArithmeticGeometry.Descent.CMVariety.RelativeGenericSmooth.Abelian

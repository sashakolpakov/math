import OAI.AlgebraicGeometry.Picard.PoincareBundle.InvariantRestriction

/-! # Invariant Comparison -/

namespace OAI.AlgebraicGeometry.Picard.PoincareBundle.InvariantComparison

noncomputable section

/-!
# Compatibility of invariant comparison maps with base change
-/

open _root_.CategoryTheory _root_.CategoryTheory.Functor _root_.CategoryTheory.Limits
open _root_.CategoryTheory.Comonad

universe u v

variable {C D E F : Type u} [Category.{v} C] [Category.{v} D]
  [Category.{v} E] [Category.{v} F]
  {L₁ : C ⥤ D} {R₁ : D ⥤ C} {L₂ : E ⥤ F} {R₂ : F ⥤ E}
  {G : C ⥤ E} {H : D ⥤ F}
  (adj₁ : L₁ ⊣ R₁) (adj₂ : L₂ ⊣ R₂) (α : G ⋙ L₂ ≅ L₁ ⋙ H)
  [IsIso (DescentRestriction.rightMate adj₁ adj₂ α)]
  [HasEqualizers C] [HasEqualizers E] [PreservesFiniteLimits G]

/-- The invariant restriction isomorphism respects the equalizer inclusion. -/
theorem invariantRestrictionIso_hom_ι (A : adj₁.toComonad.Coalgebra) :
    (InvariantRestriction.invariantRestrictionIso adj₁ adj₂ α A).hom ≫
      equalizer.ι (R₂.map ((DescentRestriction.coalgebraRestriction adj₁ adj₂ α).obj A).a)
        (adj₂.unit.app _) =
      G.map (equalizer.ι (R₁.map A.a) (adj₁.unit.app _)) ≫
        (DescentRestriction.rightMate adj₁ adj₂ α).app A.A := by
  dsimp [InvariantRestriction.invariantRestrictionIso]
  erw [Iso.trans_hom, Category.assoc]
  dsimp only [equalizer.ι]
  erw [HasLimit.isoOfNatIso_hom_π]
  change (PreservesEqualizer.iso G (R₁.map A.a) (adj₁.unit.app (R₁.obj A.A))).hom ≫
    equalizer.ι _ _ ≫ (DescentRestriction.rightMate adj₁ adj₂ α).app A.A = _
  erw [← Category.assoc, PreservesEqualizer.iso_hom, equalizerComparison_comp_π]

/-- The canonical pullback comparison commutes with the invariant
restriction isomorphism and the pullback square. -/
theorem comparison_compatibility (A : adj₁.toComonad.Coalgebra) :
    L₂.map (InvariantRestriction.invariantRestrictionIso adj₁ adj₂ α A).hom ≫
      ((ComonadicityInternal.comparisonAdjunction adj₂).counit.app
        ((DescentRestriction.coalgebraRestriction adj₁ adj₂ α).obj A)).f =
      α.hom.app (ComonadicityInternal.comparisonRightAdjointObj adj₁ A) ≫
        H.map ((ComonadicityInternal.comparisonAdjunction adj₁).counit.app A).f := by
  rw [ComonadicityInternal.comparisonAdjunction_counit_f_aux,
    ComonadicityInternal.comparisonAdjunction_counit_f_aux]
  simp only [Adjunction.homEquiv_counit]
  erw [← Category.assoc, ← L₂.map_comp,
    invariantRestrictionIso_hom_ι adj₁ adj₂ α A,
    L₂.map_comp]
  rw [Category.assoc]
  erw [mateEquiv_counit adj₁ adj₂ (TwoSquare.mk _ _ _ _ α.hom) A.A]
  erw [← Category.assoc, α.hom.naturality, Category.assoc, ← H.map_comp]
  rfl

/-- If the restricted comparison is an isomorphism, so is the image of
the original comparison under restriction. -/
theorem comparison_map_isIso (A : adj₁.toComonad.Coalgebra)
    [hc : IsIso ((ComonadicityInternal.comparisonAdjunction adj₂).counit.app
      ((DescentRestriction.coalgebraRestriction adj₁ adj₂ α).obj A)).f] :
    IsIso (H.map ((ComonadicityInternal.comparisonAdjunction adj₁).counit.app A).f) := by
  have hm : IsIso (L₂.map
      (InvariantRestriction.invariantRestrictionIso adj₁ adj₂ α A).hom) :=
    (L₂.mapIso (InvariantRestriction.invariantRestrictionIso adj₁ adj₂ α A)).isIso_hom
  have ha : IsIso (α.hom.app (ComonadicityInternal.comparisonRightAdjointObj adj₁ A)) :=
    (α.app _).isIso_hom
  have h : IsIso (α.hom.app (ComonadicityInternal.comparisonRightAdjointObj adj₁ A) ≫
      H.map ((ComonadicityInternal.comparisonAdjunction adj₁).counit.app A).f) := by
    rw [← comparison_compatibility adj₁ adj₂ α A]
    exact @IsIso.comp_isIso _ _ _ _ _ _ _ hm hc
  exact (@isIso_comp_left_iff _ _ _ _ _ _ _ ha).mp h

end

end OAI.AlgebraicGeometry.Picard.PoincareBundle.InvariantComparison

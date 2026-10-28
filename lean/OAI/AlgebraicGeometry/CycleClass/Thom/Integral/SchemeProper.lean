import OAI.AlgebraicGeometry.CycleClass.Thom.Affine.SchemeIntegralProper
import OAI.AlgebraicGeometry.CycleClass.Thom.Proper.MapOpenCover
import OAI.AlgebraicGeometry.CycleClass.Thom.ProperImage.AnalyticRestriction

/-! # Scheme Proper -/

namespace OAI.AlgebraicGeometry.CycleClass.Thom.Integral.SchemeProper.Constructions

noncomputable section

/-! Actual integral morphisms of complex schemes induce proper maps of
ordinary complex points. The proof glues the actual affine restrictions. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace

open OAI.AlgebraicGeometry.CycleClass.Thom.ProperImage.AnalyticRestriction.Constructions.Construction OAI.AlgebraicGeometry.CycleClass.Thom.Affine.SchemeIntegralProper.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.Proper.MapOpenCover.Constructions

theorem restrictedPointMap_isProperMap {X Y : Over Foundations.Scheme.ProjectiveSpace.complexBase} (f : X ⟶ Y)
    (U : Y.left.Opens) (h : IsProperMap (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map (ProperImage.AnalyticRestriction.Constructions.Construction.restrictedSchemeMap f U))) :
    IsProperMap ((ProperImage.AnalyticRestriction.Constructions.Construction.schemeAnalyticOpen Y U : Set (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints Y)).restrictPreimage
      (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map f)) := by
  let eX := ProperImage.AnalyticRestriction.Constructions.Construction.openSchemePointHomeomorph X (f.left ⁻¹ᵁ U)
  let eY := ProperImage.AnalyticRestriction.Constructions.Construction.openSchemePointHomeomorph Y U
  let F := (ProperImage.AnalyticRestriction.Constructions.Construction.schemeAnalyticOpen Y U : Set (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints Y)).restrictPreimage
    (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map f)
  have he : ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map (ProperImage.AnalyticRestriction.Constructions.Construction.restrictedSchemeMap f U) = eY.symm ∘ F ∘ eX := by
    funext x
    apply eY.injective
    rw [Function.comp_apply, Homeomorph.apply_symm_apply]
    apply Subtype.ext
    change ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map (ProperImage.AnalyticRestriction.Constructions.Construction.openSchemeInclusion Y U)
        (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map (ProperImage.AnalyticRestriction.Constructions.Construction.restrictedSchemeMap f U) x) =
      ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map f (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map (ProperImage.AnalyticRestriction.Constructions.Construction.openSchemeInclusion X (f.left ⁻¹ᵁ U)) x)
    rw [← ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map_comp, ← ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map_comp,
      ProperImage.AnalyticRestriction.Constructions.Construction.restrictedSchemeMap_inclusion]
  have hp := eY.isProperMap.comp (h.comp eX.symm.isProperMap)
  have hm : eY ∘ ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map (ProperImage.AnalyticRestriction.Constructions.Construction.restrictedSchemeMap f U) ∘ eX.symm = F := by
    rw [he]
    funext x
    simp only [Function.comp_apply, Homeomorph.apply_symm_apply]
    change F (eX (eX.symm x)) = F x
    exact congrArg F (eX.apply_symm_apply x)
  have hF : IsProperMap F := (congrArg IsProperMap hm).mp hp
  exact hF

theorem isProperMap_integral {X Y : Over Foundations.Scheme.ProjectiveSpace.complexBase} (f : X ⟶ Y)
    [IsIntegralHom f.left] [LocallyOfFiniteType Y.hom] :
    IsProperMap (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map f) := by
  let U : Y.left.affineOpens → Opens (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints Y) :=
    fun V => ProperImage.AnalyticRestriction.Constructions.Construction.schemeAnalyticOpen Y V.val
  have hU : IsOpenCover U := by
    apply IsOpenCover.mk
    apply le_antisymm le_top
    intro y _
    obtain ⟨V, hV, hy, _⟩ := exists_isAffineOpen_mem_and_subset
      (TopologicalSpace.Opens.mem_top (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.underlying y))
    exact Opens.mem_iSup.mpr ⟨⟨V, hV⟩, hy⟩
  apply Proper.MapOpenCover.Constructions.isProperMap_of_openCover hU (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.continuous_map f)
  intro V
  apply restrictedPointMap_isProperMap f V.val
  let : IsAffine (ProperImage.AnalyticRestriction.Constructions.Construction.openSchemeOver Y V.val).left := V.property
  let : IsAffine (ProperImage.AnalyticRestriction.Constructions.Construction.openSchemeOver X (f.left ⁻¹ᵁ V.val)).left := V.property.preimage f.left
  let : IsIntegralHom (ProperImage.AnalyticRestriction.Constructions.Construction.restrictedSchemeMap f V.val).left :=
    inferInstanceAs (IsIntegralHom (f.left ∣_ V.val))
  let : LocallyOfFiniteType (ProperImage.AnalyticRestriction.Constructions.Construction.openSchemeOver Y V.val).hom :=
    inferInstanceAs (LocallyOfFiniteType (V.val.ι ≫ Y.hom))
  exact Affine.SchemeIntegralProper.Constructions.isProperMap_affine_integral (ProperImage.AnalyticRestriction.Constructions.Construction.restrictedSchemeMap f V.val)

end

end OAI.AlgebraicGeometry.CycleClass.Thom.Integral.SchemeProper.Constructions

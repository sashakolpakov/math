import OAI.AlgebraicGeometry.CycleClass.Thom.Closed.SupportImageIso
import OAI.AlgebraicGeometry.CycleClass.Thom.Scheme.OpenSupportClosure
import OAI.AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs

/-! # Support Analytic Image -/

namespace OAI

noncomputable section

namespace AlgebraicGeometry.CycleClass.Thom.Closed.SupportAnalyticImage.Constructions.RegularIso

/-! The canonical isomorphism from a reduced support to its closed
image identifies their actual smooth strata over the complex base. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace

open OAI.AlgebraicGeometry.CycleClass.Thom.Scheme.ProperSupport.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.Scheme.RegularSupport.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.Scheme.SmoothSupportOpen.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.Closed.SupportImageIso.Constructions

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {X Y : Over Foundations.Scheme.ProjectiveSpace.complexBase} [LocallyOfFiniteType X.hom] [LocallyOfFiniteType Y.hom]
  (f : X ⟶ Y) [IsClosedImmersion f.left] (Z : IrreducibleCloseds X.left)

def sourceRegularToImageSupport : Scheme.RegularSupport.Constructions.regularOver X Z ⟶ Scheme.RegularSupport.Constructions.supportOver Y (Scheme.ProperSupport.Constructions.imageSupport f Z) :=
  Scheme.SmoothSupportOpen.Constructions.regularToSupport X Z ≫ (SupportImageIso.Constructions.supportImageIso f Z).hom

instance sourceRegularToImageSupport_open : IsOpenImmersion (sourceRegularToImageSupport f Z).left := by
  change IsOpenImmersion ((Scheme.SmoothSupportOpen.Constructions.regularToSupport X Z).left ≫ (SupportImageIso.Constructions.supportImageIso f Z).hom.left)
  infer_instance

def targetRegularToSourceSupport : Scheme.RegularSupport.Constructions.regularOver Y (Scheme.ProperSupport.Constructions.imageSupport f Z) ⟶ Scheme.RegularSupport.Constructions.supportOver X Z :=
  Scheme.SmoothSupportOpen.Constructions.regularToSupport Y (Scheme.ProperSupport.Constructions.imageSupport f Z) ≫ (SupportImageIso.Constructions.supportImageIso f Z).inv

instance targetRegularToSourceSupport_open : IsOpenImmersion (targetRegularToSourceSupport f Z).left := by
  change IsOpenImmersion ((Scheme.SmoothSupportOpen.Constructions.regularToSupport Y (Scheme.ProperSupport.Constructions.imageSupport f Z)).left ≫ (SupportImageIso.Constructions.supportImageIso f Z).inv.left)
  infer_instance

def regularImageMap : Scheme.RegularSupport.Constructions.regularOver X Z ⟶ Scheme.RegularSupport.Constructions.regularOver Y (Scheme.ProperSupport.Constructions.imageSupport f Z) :=
  Scheme.OpenSupportClosure.Constructions.smoothOpenToRegular (Scheme.ProperSupport.Constructions.imageSupport f Z) (sourceRegularToImageSupport f Z)

def regularImageInverse : Scheme.RegularSupport.Constructions.regularOver Y (Scheme.ProperSupport.Constructions.imageSupport f Z) ⟶ Scheme.RegularSupport.Constructions.regularOver X Z :=
  Scheme.OpenSupportClosure.Constructions.smoothOpenToRegular Z (targetRegularToSourceSupport f Z)

theorem regularImageMap_inclusion :
    regularImageMap f Z ≫ Scheme.SmoothSupportOpen.Constructions.regularToSupport Y (Scheme.ProperSupport.Constructions.imageSupport f Z) =
      Scheme.SmoothSupportOpen.Constructions.regularToSupport X Z ≫ (SupportImageIso.Constructions.supportImageIso f Z).hom :=
  Scheme.OpenSupportClosure.Constructions.smoothOpenToRegular_inclusion (Scheme.ProperSupport.Constructions.imageSupport f Z) (sourceRegularToImageSupport f Z)

theorem regularImageInverse_inclusion :
    regularImageInverse f Z ≫ Scheme.SmoothSupportOpen.Constructions.regularToSupport X Z =
      Scheme.SmoothSupportOpen.Constructions.regularToSupport Y (Scheme.ProperSupport.Constructions.imageSupport f Z) ≫ (SupportImageIso.Constructions.supportImageIso f Z).inv :=
  Scheme.OpenSupportClosure.Constructions.smoothOpenToRegular_inclusion Z (targetRegularToSourceSupport f Z)

theorem regularImageMap_inverse : regularImageMap f Z ≫ regularImageInverse f Z = 𝟙 _ := by
  let : Mono (Scheme.SmoothSupportOpen.Constructions.regularToSupport X Z) := (Over.forget Foundations.Scheme.ProjectiveSpace.complexBase).mono_of_mono_map
    (inferInstanceAs (Mono (Scheme.SmoothSupportOpen.Constructions.regularToSupport X Z).left))
  apply (cancel_mono (Scheme.SmoothSupportOpen.Constructions.regularToSupport X Z)).mp
  rw [Category.assoc, regularImageInverse_inclusion, ← Category.assoc, regularImageMap_inclusion,
    Category.assoc, Iso.hom_inv_id, Category.comp_id, Category.id_comp]

theorem regularImageInverse_map : regularImageInverse f Z ≫ regularImageMap f Z = 𝟙 _ := by
  let : Mono (Scheme.SmoothSupportOpen.Constructions.regularToSupport Y (Scheme.ProperSupport.Constructions.imageSupport f Z)) := (Over.forget Foundations.Scheme.ProjectiveSpace.complexBase).mono_of_mono_map
    (inferInstanceAs (Mono (Scheme.SmoothSupportOpen.Constructions.regularToSupport Y (Scheme.ProperSupport.Constructions.imageSupport f Z)).left))
  apply (cancel_mono (Scheme.SmoothSupportOpen.Constructions.regularToSupport Y (Scheme.ProperSupport.Constructions.imageSupport f Z))).mp
  rw [Category.assoc, regularImageMap_inclusion, ← Category.assoc, regularImageInverse_inclusion,
    Category.assoc, Iso.inv_hom_id, Category.comp_id, Category.id_comp]

def regularSupportImageIso : Scheme.RegularSupport.Constructions.regularOver X Z ≅ Scheme.RegularSupport.Constructions.regularOver Y (Scheme.ProperSupport.Constructions.imageSupport f Z) where
  hom := regularImageMap f Z
  inv := regularImageInverse f Z
  hom_inv_id := regularImageMap_inverse f Z
  inv_hom_id := regularImageInverse_map f Z

theorem regularSupportImageIso_ambient :
    (regularSupportImageIso f Z).hom ≫ Scheme.RegularSupport.Constructions.regularToAmbient Y (Scheme.ProperSupport.Constructions.imageSupport f Z) = Scheme.RegularSupport.Constructions.regularToAmbient X Z ≫ f := by
  change regularImageMap f Z ≫ Scheme.RegularSupport.Constructions.regularToAmbient Y (Scheme.ProperSupport.Constructions.imageSupport f Z) = _
  rw [← Scheme.SmoothSupportOpen.Constructions.regularToSupport_ambient, ← Category.assoc, regularImageMap_inclusion,
    Category.assoc, SupportImageIso.Constructions.supportImageIso_inclusion, ← Category.assoc, Scheme.SmoothSupportOpen.Constructions.regularToSupport_ambient]

end AlgebraicGeometry.CycleClass.Thom.Closed.SupportAnalyticImage.Constructions.RegularIso

namespace AlgebraicGeometry.CycleClass.Thom.Closed.SupportAnalyticImage.Constructions

/-! Actual full supports, regular loci, and singular boundaries are
carried to their actual analytic images by a closed algebraic immersion. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace

open OAI.AlgebraicGeometry.CycleClass.Thom.Scheme.ProperSupport.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.Scheme.RegularSupport.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.Closed.SupportImageIso.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.Closed.SupportAnalyticImage.Constructions.RegularIso

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {X Y : Over Foundations.Scheme.ProjectiveSpace.complexBase} [LocallyOfFiniteType X.hom] [LocallyOfFiniteType Y.hom]
  (f : X ⟶ Y) [IsClosedImmersion f.left] (Z : IrreducibleCloseds X.left)

omit [LocallyOfFiniteType X.hom] [LocallyOfFiniteType Y.hom] in
theorem supportMap_apply (t : ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints (Scheme.RegularSupport.Constructions.supportOver X Z)) :
    Scheme.RegularSupport.Constructions.supportInclusion Y (Scheme.ProperSupport.Constructions.imageSupport f Z) (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map (SupportImageIso.Constructions.supportImageIso f Z).hom t) =
      ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map f (Scheme.RegularSupport.Constructions.supportInclusion X Z t) := by
  have h := congrArg (fun k : Scheme.RegularSupport.Constructions.supportOver X Z ⟶ Y => ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map k t) (SupportImageIso.Constructions.supportImageIso_inclusion f Z)
  simpa only [ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map_comp] using h

omit [LocallyOfFiniteType X.hom] [LocallyOfFiniteType Y.hom] in
theorem supportImage_range : Set.range (Scheme.RegularSupport.Constructions.supportInclusion Y (Scheme.ProperSupport.Constructions.imageSupport f Z)) =
    Set.range (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map f ∘ Scheme.RegularSupport.Constructions.supportInclusion X Z) := by
  ext y
  constructor
  · rintro ⟨u, rfl⟩
    let t := (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.isoHomeomorph (SupportImageIso.Constructions.supportImageIso f Z)).symm u
    refine ⟨t, (supportMap_apply f Z t).symm.trans ?_⟩
    exact congrArg (Scheme.RegularSupport.Constructions.supportInclusion Y (Scheme.ProperSupport.Constructions.imageSupport f Z))
      ((ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.isoHomeomorph (SupportImageIso.Constructions.supportImageIso f Z)).apply_symm_apply u)
  · rintro ⟨t, rfl⟩
    exact ⟨ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map (SupportImageIso.Constructions.supportImageIso f Z).hom t, supportMap_apply f Z t⟩

theorem regularMap_apply (t : ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints (Scheme.RegularSupport.Constructions.regularOver X Z)) :
    Scheme.RegularSupport.Constructions.regularInclusion Y (Scheme.ProperSupport.Constructions.imageSupport f Z) (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map (RegularIso.regularSupportImageIso f Z).hom t) =
      ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map f (Scheme.RegularSupport.Constructions.regularInclusion X Z t) := by
  have h := congrArg (fun k : Scheme.RegularSupport.Constructions.regularOver X Z ⟶ Y => ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map k t) (RegularIso.regularSupportImageIso_ambient f Z)
  simpa only [ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map_comp] using h

theorem regularImage_range : Set.range (Scheme.RegularSupport.Constructions.regularInclusion Y (Scheme.ProperSupport.Constructions.imageSupport f Z)) =
    Set.range (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map f ∘ Scheme.RegularSupport.Constructions.regularInclusion X Z) := by
  ext y
  constructor
  · rintro ⟨u, rfl⟩
    let t := (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.isoHomeomorph (RegularIso.regularSupportImageIso f Z)).symm u
    refine ⟨t, (regularMap_apply f Z t).symm.trans ?_⟩
    exact congrArg (Scheme.RegularSupport.Constructions.regularInclusion Y (Scheme.ProperSupport.Constructions.imageSupport f Z))
      ((ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.isoHomeomorph (RegularIso.regularSupportImageIso f Z)).apply_symm_apply u)
  · rintro ⟨t, rfl⟩
    exact ⟨ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map (RegularIso.regularSupportImageIso f Z).hom t, regularMap_apply f Z t⟩

theorem analyticBoundary_image : Scheme.RegularSupport.Constructions.analyticBoundary Y (Scheme.ProperSupport.Constructions.imageSupport f Z) =
    ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map f '' Scheme.RegularSupport.Constructions.analyticBoundary X Z := by
  rw [Scheme.RegularSupport.Constructions.analyticBoundary_eq, supportImage_range, regularImage_range, Set.range_comp, Set.range_comp,
    Scheme.RegularSupport.Constructions.analyticBoundary_eq, Set.image_sdiff (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.isClosedEmbedding_map_of_isClosedImmersion f).injective]

end AlgebraicGeometry.CycleClass.Thom.Closed.SupportAnalyticImage.Constructions

end

end OAI

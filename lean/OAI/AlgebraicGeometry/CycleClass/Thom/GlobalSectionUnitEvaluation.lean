import OAI.AlgebraicGeometry.CycleClass.Thom.GlobalSectionUnitRepresentative
import OAI.AlgebraicGeometry.CycleClass.Thom.GlobalSectionBasicOpen

/-! # Global Section Unit Evaluation -/

namespace OAI

noncomputable section

namespace AlgebraicGeometry.CycleClass.Thom.GlobalSectionUnitEvaluation.Constructions

/-! The constructed full unit representative evaluates to the original
global regular section on its whole analytic nonvanishing locus. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace

open OAI.AlgebraicGeometry.CycleClass.Thom.Scheme.SectionEvaluation.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.GlobalSectionUnitRepresentative.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.GlobalSectionBasicOpen.Constructions

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable (X : Over Foundations.Scheme.ProjectiveSpace.complexBase)

theorem restriction_topIso (U : X.left.Opens) :
    X.left.presheaf.map (homOfLE (show U ≤ ⊤ from le_top)).op ≫ U.topIso.inv = U.ι.appTop := by
  simp only [Scheme.Opens.topIso_inv, Scheme.Opens.ι_appTop, ← Functor.map_comp]
  congr 1

theorem sectionEvaluationOn_globalRestriction (U : X.left.Opens) (s : Γ(X.left, ⊤)) (x : Thom.Scheme.SectionEvaluation.Constructions.analyticOpen X U) :
    Thom.Scheme.SectionEvaluation.Constructions.sectionEvaluationOn X U (X.left.presheaf.map (homOfLE (show U ≤ ⊤ from le_top)).op s) x =
      DivisorClass.Chern.AnalyticTransitions.Construction.globalSectionEvaluation x.val s := by
  have h := Thom.Scheme.SectionEvaluation.Constructions.openPointHomeomorph_val X U ((Thom.Scheme.SectionEvaluation.Constructions.openPointHomeomorph X U).symm x)
  have hx : ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map (Thom.Scheme.SectionEvaluation.Constructions.openInclusion X U) ((Thom.Scheme.SectionEvaluation.Constructions.openPointHomeomorph X U).symm x) = x.val := by
    simpa only [Homeomorph.apply_symm_apply] using h.symm
  change DivisorClass.Chern.AnalyticTransitions.Construction.globalSectionEvaluation ((Thom.Scheme.SectionEvaluation.Constructions.openPointHomeomorph X U).symm x)
    (U.topIso.inv (X.left.presheaf.map (homOfLE (show U ≤ ⊤ from le_top)).op s)) = _
  rw [← hx, DivisorClass.Chern.AnalyticTransitions.Construction.globalSectionEvaluation_map]
  exact congrArg (DivisorClass.Chern.AnalyticTransitions.Construction.globalSectionEvaluation ((Thom.Scheme.SectionEvaluation.Constructions.openPointHomeomorph X U).symm x))
    (ConcreteCategory.congr_hom (restriction_topIso X U) s)

variable [IsIntegral X.left]

local instance : Nonempty (⊤ : X.left.Opens) := ⟨⟨genericPoint X.left, Opens.mem_top _⟩⟩

variable (s : Γ(X.left, ⊤)) (hs : X.left.germToFunctionField ⊤ s ≠ 0)

theorem sectionUnitRepresentative_evaluation
    (x : Thom.Scheme.SectionEvaluation.Constructions.analyticOpen X (GlobalSectionUnitRepresentative.Constructions.sectionUnitRepresentative X.left s hs).domain) :
    Thom.Scheme.SectionEvaluation.Constructions.sectionEvaluationOn X (GlobalSectionUnitRepresentative.Constructions.sectionUnitRepresentative X.left s hs).domain
      (GlobalSectionUnitRepresentative.Constructions.sectionUnitRepresentative X.left s hs).unit.val x = DivisorClass.Chern.AnalyticTransitions.Construction.globalSectionEvaluation x.val s := by
  change Thom.Scheme.SectionEvaluation.Constructions.sectionEvaluationOn X (X.left.basicOpen s) (GlobalSectionUnitRepresentative.Constructions.sectionUnitRepresentative X.left s hs).unit.val x = _
  rw [GlobalSectionUnitRepresentative.Constructions.sectionUnitRepresentative_unit]
  exact sectionEvaluationOn_globalRestriction X (X.left.basicOpen s) s x

theorem nonzeroEvaluation_mem_unitDomain (x : ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X) (hx : DivisorClass.Chern.AnalyticTransitions.Construction.globalSectionEvaluation x s ≠ 0) :
    x ∈ (Thom.Scheme.SectionEvaluation.Constructions.analyticOpen X (GlobalSectionUnitRepresentative.Constructions.sectionUnitRepresentative X.left s hs).domain : Set (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X)) :=
  (GlobalSectionBasicOpen.Constructions.underlying_mem_basicOpen_iff X s x).mpr hx

end AlgebraicGeometry.CycleClass.Thom.GlobalSectionUnitEvaluation.Constructions

namespace AlgebraicGeometry.CycleClass.Thom.GlobalSectionUnitEvaluation.Constructions.SchemeEquation

/-! A genuine global regular section supplies its continuous equation,
actual zero support, and full source unit representative under pullback. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace

open OAI.AlgebraicGeometry.CycleClass.Thom.GlobalSectionUnitRepresentative.Constructions
open OAI.AlgebraicGeometry.CycleClass.Thom.GlobalSectionUnitEvaluation.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.Scheme.SectionEvaluation.Constructions

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable (Y : Over Foundations.Scheme.ProjectiveSpace.complexBase) (s : Γ(Y.left, ⊤))

def sectionEquation : TopCat.of (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints Y) ⟶ PrincipalBoundary.Constructions.normalComplexLine :=
  TopCat.ofHom ⟨fun x _ => DivisorClass.Chern.AnalyticTransitions.Construction.globalSectionEvaluation x s,
    continuous_pi (fun _ => DivisorClass.Chern.AnalyticTransitions.Construction.continuous_globalSectionEvaluation Y s)⟩

def sectionZeroImage : {x : ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints Y | DivisorClass.Chern.AnalyticTransitions.Construction.globalSectionEvaluation x s = 0} → ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints Y :=
  Subtype.val

theorem sectionZeroImage_range : Set.range (sectionZeroImage Y s) = {x | DivisorClass.Chern.AnalyticTransitions.Construction.globalSectionEvaluation x s = 0} :=
  Subtype.range_coe

theorem sectionZeroImage_openComplement : IsOpen (Set.range (sectionZeroImage Y s))ᶜ := by
  rw [sectionZeroImage_range]
  exact (isClosed_eq (DivisorClass.Chern.AnalyticTransitions.Construction.continuous_globalSectionEvaluation Y s) continuous_const).isOpen_compl

theorem sectionEquation_mapsTo : Set.MapsTo (sectionEquation Y s) (Set.range (sectionZeroImage Y s))ᶜ PrincipalBoundary.Constructions.puncturedComplexLine := by
  intro x hx heq
  apply hx
  refine ⟨⟨x, ?_⟩, rfl⟩
  exact congrFun (show sectionEquation Y s x = 0 from heq) 0

variable {Y} {X : Over Foundations.Scheme.ProjectiveSpace.complexBase} [IsIntegral X.left] (g : X ⟶ Y)

local instance : Nonempty (⊤ : X.left.Opens) := ⟨⟨genericPoint X.left, Opens.mem_top _⟩⟩

variable (hs : X.left.germToFunctionField ⊤ (g.left.appTop s) ≠ 0)

theorem pullback_nonzero_mem_unitDomain :
    ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map g ⁻¹' (Set.range (sectionZeroImage Y s))ᶜ ⊆
      (Thom.Scheme.SectionEvaluation.Constructions.analyticOpen X (GlobalSectionUnitRepresentative.Constructions.sectionUnitRepresentative X.left (g.left.appTop s) hs).domain : Set (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X)) := by
  intro x hx
  apply nonzeroEvaluation_mem_unitDomain X (g.left.appTop s) hs x
  intro heq
  apply hx
  refine ⟨⟨ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map g x, ?_⟩, rfl⟩
  change DivisorClass.Chern.AnalyticTransitions.Construction.globalSectionEvaluation (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map g x) s = 0
  rw [DivisorClass.Chern.AnalyticTransitions.Construction.globalSectionEvaluation_map]
  exact heq

theorem sectionEquation_pullback_unit
    (x : ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map g ⁻¹' (Set.range (sectionZeroImage Y s))ᶜ) :
    sectionEquation Y s (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map g x.val) 0 =
      Thom.Scheme.SectionEvaluation.Constructions.sectionEvaluationOn X (GlobalSectionUnitRepresentative.Constructions.sectionUnitRepresentative X.left (g.left.appTop s) hs).domain
        (GlobalSectionUnitRepresentative.Constructions.sectionUnitRepresentative X.left (g.left.appTop s) hs).unit.val
        ⟨x.val, pullback_nonzero_mem_unitDomain s g hs x.property⟩ := by
  change DivisorClass.Chern.AnalyticTransitions.Construction.globalSectionEvaluation (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map g x.val) s = _
  rw [DivisorClass.Chern.AnalyticTransitions.Construction.globalSectionEvaluation_map]
  exact (sectionUnitRepresentative_evaluation X (g.left.appTop s) hs
    ⟨x.val, pullback_nonzero_mem_unitDomain s g hs x.property⟩).symm

end AlgebraicGeometry.CycleClass.Thom.GlobalSectionUnitEvaluation.Constructions.SchemeEquation

end

end OAI

import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.ProductDimension
import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Principal.ClosedSectionCycle
import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Grading
import Mathlib.AlgebraicGeometry.ZariskisMainTheorem

/-! # Graph -/

namespace OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Graph

noncomputable section

/-! The graph defined by the chosen product is an actual closed
immersion. For an integral source, its reduced image support is
canonically isomorphic to the source scheme. -/

set_option backward.isDefEq.respectTransparency false

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace

open OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.ProperCycleLinearity

variable {X Y : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation} (P : ProperCycleLinearity.ProductPresentation X Y) (f : X.toOver ⟶ Y.toOver)

theorem graph_fst_left : (P.graph f).left ≫ P.fst.left = 𝟙 X.carrier :=
  congrArg Over.Hom.left (P.graph_fst f)

instance graph_isClosedImmersion : IsClosedImmersion (P.graph f).left := by
  let : IsProper (P.graph f).left := ProperCycleLinearity.morphism_isProper (P.graph f)
  let : IsSplitMono (P.graph f).left := ⟨⟨⟨P.fst.left, graph_fst_left P f⟩⟩⟩
  exact (IsClosedImmersion.iff_isProper_and_mono _).mpr ⟨inferInstance, inferInstance⟩

variable [IsIntegral X.carrier]

def support : IrreducibleCloseds P.space.carrier :=
  CycleClass.Geometric.StratumClosure.integralImageClosure (Y := X.carrier) (X := P.space.carrier) (P.graph f).left

theorem support_point : CycleClass.Thom.IntersectionGeometry.supportPoint (support P f) = (P.graph f).left (genericPoint X.carrier) := by
  have h := (genericPoint_spec X.carrier).image (P.graph f).left.continuous
  simp only [Set.image_univ] at h
  exact ((support P f).isIrreducible.isGenericPoint_genericPoint (support P f).isClosed).eq h

def supportIso : X.carrier ≅ CycleClass.Geometric.GenericPoint.reducedSupportScheme (support P f) := by
  have hk : (CycleClass.Geometric.GenericPoint.reducedSupportι (support P f)).ker = (P.graph f).left.ker := by
    change (CycleClass.Geometric.GenericPoint.reducedSupportIdeal (support P f)).subschemeι.ker = _
    rw [Scheme.IdealSheafData.ker_subschemeι,
      CycleClass.Geometric.StratumClosure.kernel_eq_reducedImageClosureIdeal (Y := X.carrier) (X := P.space.carrier) (P.graph f).left]
    rfl
  let i := IsClosedImmersion.lift (CycleClass.Geometric.GenericPoint.reducedSupportι (support P f)) (P.graph f).left hk.le
  let : IsIso i := IsClosedImmersion.isIso_lift (CycleClass.Geometric.GenericPoint.reducedSupportι (support P f)) (P.graph f).left hk
  exact asIso i

theorem supportIso_fac : (supportIso P f).hom ≫ CycleClass.Geometric.GenericPoint.reducedSupportι (support P f) = (P.graph f).left :=
  IsClosedImmersion.lift_fac _ _ _

theorem supportIso_over : (supportIso P f).hom ≫ CycleClass.Geometric.SupportFiniteType.supportStructureMap (support P f) P.space.structureMap =
    X.structureMap := by
  rw [CycleClass.Geometric.SupportFiniteType.supportStructureMap, ← Category.assoc, supportIso_fac]
  exact (P.graph f).w

theorem support_codimension (m n : ℕ) [SmoothOfRelativeDimension m X.structureMap]
    [SmoothOfRelativeDimension n Y.structureMap] : P.space.supportCodimension (support P f) = n := by
  let : SmoothOfRelativeDimension (m + n) P.space.structureMap := ProductDimension.relativeDimension P m n
  have he := Foundations.Scheme.OpenFunctionField.schemeTranscendenceDimension_openImmersion (supportIso P f).hom
    (CycleClass.Geometric.SupportFiniteType.supportStructureMap (support P f) P.space.structureMap)
  rw [supportIso_over] at he
  have hm := Grading.integral_dimension_of_relativeDimension X.structureMap m
  have hg := Grading.supportDimension_add_codimension P.space (m + n) (support P f)
  change Foundations.Scheme.TranscendenceDimension.schemeTranscendenceDimension (CycleClass.Geometric.SupportFiniteType.supportStructureMap (support P f) P.space.structureMap) +
    P.space.supportCodimension (support P f) = m + n at hg
  rw [← he, hm] at hg
  omega

end

end OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Graph

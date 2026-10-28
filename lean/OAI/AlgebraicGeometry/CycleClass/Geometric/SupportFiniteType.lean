import OAI.AlgebraicGeometry.CycleClass.Geometric.GenericPoint
import OAI.AlgebraicGeometry.Foundations.Scheme.ClosedProjective

/-! # Support Finite Type -/

namespace OAI.AlgebraicGeometry

noncomputable section

/-!
# Finite presentation and projectivity of integral cycle supports

The structure morphism on a cycle support is the composite of its actual
closed immersion with the ambient structure morphism. Finite type and, over
a locally Noetherian base, local finite presentation follow from this map.
The support also inherits a genuine projective presentation. No smoothness
of the possibly singular support is assumed.
-/

open _root_.AlgebraicGeometry _root_.CategoryTheory _root_.TopologicalSpace

universe u

variable {X S : Scheme.{u}}

/-- A cycle support has the structure morphism induced by its closed immersion. -/
def CycleClass.Geometric.SupportFiniteType.supportStructureMap (Z : IrreducibleCloseds X) (f : X ⟶ S) :
    CycleClass.Geometric.GenericPoint.reducedSupportScheme Z ⟶ S :=
  CycleClass.Geometric.GenericPoint.reducedSupportι Z ≫ f

instance CycleClass.Geometric.SupportFiniteType.reducedSupportι_locallyOfFiniteType (Z : IrreducibleCloseds X) :
    LocallyOfFiniteType (CycleClass.Geometric.GenericPoint.reducedSupportι Z) := by
  infer_instance

instance CycleClass.Geometric.SupportFiniteType.reducedSupportι_quasiCompact (Z : IrreducibleCloseds X) :
    QuasiCompact (CycleClass.Geometric.GenericPoint.reducedSupportι Z) := by
  infer_instance

instance CycleClass.Geometric.SupportFiniteType.reducedSupportι_locallyOfFinitePresentation (Z : IrreducibleCloseds X)
    [IsLocallyNoetherian X] : LocallyOfFinitePresentation (CycleClass.Geometric.GenericPoint.reducedSupportι Z) := by
  infer_instance

instance CycleClass.Geometric.SupportFiniteType.reducedSupportScheme_isLocallyNoetherian (Z : IrreducibleCloseds X)
    [IsLocallyNoetherian X] : IsLocallyNoetherian (CycleClass.Geometric.GenericPoint.reducedSupportScheme Z) :=
  LocallyOfFiniteType.isLocallyNoetherian (CycleClass.Geometric.GenericPoint.reducedSupportι Z)

/-- Compactness here is compactness of the underlying Zariski space. -/
instance CycleClass.Geometric.SupportFiniteType.reducedSupportScheme_compactSpace (Z : IrreducibleCloseds X)
    [CompactSpace X] : CompactSpace (CycleClass.Geometric.GenericPoint.reducedSupportScheme Z) :=
  QuasiCompact.compactSpace_of_compactSpace (CycleClass.Geometric.GenericPoint.reducedSupportι Z)

instance CycleClass.Geometric.SupportFiniteType.reducedSupportScheme_isNoetherian (Z : IrreducibleCloseds X)
    [IsNoetherian X] : IsNoetherian (CycleClass.Geometric.GenericPoint.reducedSupportScheme Z) where

instance CycleClass.Geometric.SupportFiniteType.supportStructureMap_locallyOfFiniteType (Z : IrreducibleCloseds X)
    (f : X ⟶ S) [LocallyOfFiniteType f] :
    LocallyOfFiniteType (CycleClass.Geometric.SupportFiniteType.supportStructureMap Z f) := by
  unfold CycleClass.Geometric.SupportFiniteType.supportStructureMap
  infer_instance

instance CycleClass.Geometric.SupportFiniteType.supportStructureMap_quasiCompact (Z : IrreducibleCloseds X)
    (f : X ⟶ S) [QuasiCompact f] : QuasiCompact (CycleClass.Geometric.SupportFiniteType.supportStructureMap Z f) := by
  unfold CycleClass.Geometric.SupportFiniteType.supportStructureMap
  infer_instance

/-- Over a locally Noetherian base, finite type supplies local finite
presentation for the support, with no regularity assumption on it. -/
instance CycleClass.Geometric.SupportFiniteType.supportStructureMap_locallyOfFinitePresentation (Z : IrreducibleCloseds X)
    (f : X ⟶ S) [IsLocallyNoetherian S] [LocallyOfFiniteType f] :
    LocallyOfFinitePresentation (CycleClass.Geometric.SupportFiniteType.supportStructureMap Z f) := by
  infer_instance

/-- Both conditions in the usual definition of finite type hold for the
support whenever they hold for its ambient scheme morphism. -/
theorem CycleClass.Geometric.SupportFiniteType.supportStructureMap_finiteType (Z : IrreducibleCloseds X)
    (f : X ⟶ S) [LocallyOfFiniteType f] [QuasiCompact f] :
    LocallyOfFiniteType (CycleClass.Geometric.SupportFiniteType.supportStructureMap Z f) ∧
      QuasiCompact (CycleClass.Geometric.SupportFiniteType.supportStructureMap Z f) :=
  ⟨inferInstance, inferInstance⟩

section

variable {X : Scheme} {f : X ⟶ Foundations.Scheme.ProjectiveSpace.complexBase}

/-- A closed integral support inherits the actual ambient projective embedding. -/
def Foundations.Scheme.SmoothProjective.ProjectivePresentation.reducedSupport (P : Foundations.Scheme.SmoothProjective.ProjectivePresentation X f) (Z : IrreducibleCloseds X) :
    Foundations.Scheme.SmoothProjective.ProjectivePresentation (CycleClass.Geometric.GenericPoint.reducedSupportScheme Z) (CycleClass.Geometric.SupportFiniteType.supportStructureMap Z f) where
  ambientDimension := P.ambientDimension
  embedding := CycleClass.Geometric.GenericPoint.reducedSupportι Z ≫ P.embedding
  closedImmersion := by infer_instance
  over_base := by
    dsimp only [CycleClass.Geometric.SupportFiniteType.supportStructureMap]
    rw [Category.assoc, P.over_base]

/-- Noetherianity of each support follows from the genuine projective embedding. -/
theorem Foundations.Scheme.SmoothProjective.ProjectivePresentation.reducedSupport_isNoetherian (P : Foundations.Scheme.SmoothProjective.ProjectivePresentation X f)
    (Z : IrreducibleCloseds X) : IsNoetherian (CycleClass.Geometric.GenericPoint.reducedSupportScheme Z) :=
  (P.reducedSupport Z).isNoetherian

/-- Each support is locally of finite presentation over the complex base. -/
theorem Foundations.Scheme.SmoothProjective.ProjectivePresentation.reducedSupport_locallyOfFinitePresentation (P : Foundations.Scheme.SmoothProjective.ProjectivePresentation X f)
    (Z : IrreducibleCloseds X) : LocallyOfFinitePresentation (CycleClass.Geometric.SupportFiniteType.supportStructureMap Z f) :=
  (P.reducedSupport Z).locallyOfFinitePresentation

/-- Each support is proper over the complex base. -/
theorem Foundations.Scheme.SmoothProjective.ProjectivePresentation.reducedSupport_isProper (P : Foundations.Scheme.SmoothProjective.ProjectivePresentation X f)
    (Z : IrreducibleCloseds X) : IsProper (CycleClass.Geometric.SupportFiniteType.supportStructureMap Z f) :=
  (P.reducedSupport Z).isProper

/-- The three standard conditions for a finitely presented morphism all hold
for this projective support: local finite presentation, quasi-compactness, and
quasi-separatedness. -/
theorem Foundations.Scheme.SmoothProjective.ProjectivePresentation.reducedSupport_finitePresentation (P : Foundations.Scheme.SmoothProjective.ProjectivePresentation X f)
    (Z : IrreducibleCloseds X) :
    LocallyOfFinitePresentation (CycleClass.Geometric.SupportFiniteType.supportStructureMap Z f) ∧
      QuasiCompact (CycleClass.Geometric.SupportFiniteType.supportStructureMap Z f) ∧
        QuasiSeparated (CycleClass.Geometric.SupportFiniteType.supportStructureMap Z f) := by
  let : IsProper (CycleClass.Geometric.SupportFiniteType.supportStructureMap Z f) := P.reducedSupport_isProper Z
  exact ⟨P.reducedSupport_locallyOfFinitePresentation Z, inferInstance, inferInstance⟩

end

/-- An actual codimension-indexed support in a smooth projective presentation
has a locally finitely presented structure map over `Spec ℂ`. -/
theorem Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation.cycleSupport_locallyOfFinitePresentation (P : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation)
    (p : ℕ) (Z : Foundations.Scheme.CycleSupports.IrreducibleCycleSupport P.carrier p) :
    LocallyOfFinitePresentation (CycleClass.Geometric.SupportFiniteType.supportStructureMap Z.1 P.structureMap) :=
  P.projective.reducedSupport_locallyOfFinitePresentation Z.1

/-- The integral closed scheme underlying an actual cycle support is Noetherian. -/
theorem Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation.cycleSupport_isNoetherian (P : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation)
    (p : ℕ) (Z : Foundations.Scheme.CycleSupports.IrreducibleCycleSupport P.carrier p) :
    IsNoetherian (CycleClass.Geometric.GenericPoint.reducedSupportScheme Z.1) :=
  P.projective.reducedSupport_isNoetherian Z.1

end

end OAI.AlgebraicGeometry

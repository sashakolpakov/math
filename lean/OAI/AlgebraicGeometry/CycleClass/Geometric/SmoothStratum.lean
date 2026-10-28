import OAI.AlgebraicGeometry.CycleClass.Geometric.SingularCodimension
import Mathlib.AlgebraicGeometry.Morphisms.Immersion

/-! # Smooth Stratum -/

namespace OAI.AlgebraicGeometry

noncomputable section

/-!
# The actual smooth stratum of an algebraic cycle support

The smooth stratum is the open subscheme cut out by the smooth locus of the
actual structure morphism. Its smoothness is proved from restriction of the
smooth locus. For an integral cycle support over a perfect field it is dense,
and its complement has strictly larger ambient codimension.
-/

open _root_.AlgebraicGeometry _root_.CategoryTheory _root_.TopologicalSpace

universe u

variable {X Y : Scheme.{u}}

/-- The open subscheme consisting of smooth points of an actual morphism. -/
def CycleClass.Geometric.SmoothStratum.smoothStratum (f : X ⟶ Y) [LocallyOfFinitePresentation f] : Scheme.{u} :=
  f.smoothLocus.toScheme

/-- The actual open immersion from the smooth stratum to its source scheme. -/
def CycleClass.Geometric.SmoothStratum.smoothStratumι (f : X ⟶ Y) [LocallyOfFinitePresentation f] :
    CycleClass.Geometric.SmoothStratum.smoothStratum f ⟶ X :=
  f.smoothLocus.ι

/-- The restriction of the structure morphism to its smooth stratum. -/
def CycleClass.Geometric.SmoothStratum.smoothStratumToBase (f : X ⟶ Y) [LocallyOfFinitePresentation f] :
    CycleClass.Geometric.SmoothStratum.smoothStratum f ⟶ Y :=
  CycleClass.Geometric.SmoothStratum.smoothStratumι f ≫ f

instance CycleClass.Geometric.SmoothStratum.smoothStratumι_isOpenImmersion (f : X ⟶ Y)
    [LocallyOfFinitePresentation f] : IsOpenImmersion (CycleClass.Geometric.SmoothStratum.smoothStratumι f) :=
  inferInstanceAs (IsOpenImmersion f.smoothLocus.ι)

/-- Smoothness is proved, not included as an assumed field of a stratum. -/
instance CycleClass.Geometric.SmoothStratum.smoothStratumToBase_isSmooth (f : X ⟶ Y)
    [LocallyOfFinitePresentation f] : Smooth (CycleClass.Geometric.SmoothStratum.smoothStratumToBase f) := by
  change Smooth (f.smoothLocus.ι ≫ f)
  apply Scheme.Hom.smoothLocus_eq_top_iff.mp
  rw [← Scheme.Hom.preimage_smoothLocus_eq]
  exact Scheme.Opens.ι_preimage_self _

@[simp]
theorem CycleClass.Geometric.SmoothStratum.range_smoothStratumι (f : X ⟶ Y) [LocallyOfFinitePresentation f] :
    Set.range (CycleClass.Geometric.SmoothStratum.smoothStratumι f) = (f.smoothLocus : Set X) :=
  Scheme.Opens.range_ι _

/-- The omitted points are exactly the previously defined singular locus. -/
theorem CycleClass.Geometric.SmoothStratum.smoothStratum_complement (f : X ⟶ Y) [LocallyOfFinitePresentation f] :
    (Set.range (CycleClass.Geometric.SmoothStratum.smoothStratumι f))ᶜ = CycleClass.Geometric.SingularLocus.singularLocus f := by
  rw [CycleClass.Geometric.SmoothStratum.range_smoothStratumι]
  rfl

/-- The smooth open stratum of a reduced support is a locally closed subscheme
of the original ambient scheme. -/
def CycleClass.Geometric.SmoothStratum.reducedSupportSmoothStratumι (Z : IrreducibleCloseds X)
    (f : CycleClass.Geometric.GenericPoint.reducedSupportScheme Z ⟶ Y) [LocallyOfFinitePresentation f] :
    CycleClass.Geometric.SmoothStratum.smoothStratum f ⟶ X :=
  CycleClass.Geometric.SmoothStratum.smoothStratumι f ≫ CycleClass.Geometric.GenericPoint.reducedSupportι Z

instance CycleClass.Geometric.SmoothStratum.reducedSupportSmoothStratumι_isImmersion (Z : IrreducibleCloseds X)
    (f : CycleClass.Geometric.GenericPoint.reducedSupportScheme Z ⟶ Y) [LocallyOfFinitePresentation f] :
    IsImmersion (CycleClass.Geometric.SmoothStratum.reducedSupportSmoothStratumι Z f) := by
  unfold CycleClass.Geometric.SmoothStratum.reducedSupportSmoothStratumι
  infer_instance

variable {K : Type u} [Field K] [PerfectField K]

/-- Generic smoothness gives a dense range in every reduced source over a
perfect field. -/
theorem CycleClass.Geometric.SmoothStratum.smoothStratum_denseRange [IsReduced X]
    (f : X ⟶ Spec (.of K)) [LocallyOfFinitePresentation f] :
    DenseRange (CycleClass.Geometric.SmoothStratum.smoothStratumι f) := by
  change Dense (Set.range (CycleClass.Geometric.SmoothStratum.smoothStratumι f))
  rw [CycleClass.Geometric.SmoothStratum.range_smoothStratumι]
  exact f.dense_smoothLocus_of_perfectField

instance CycleClass.Geometric.SmoothStratum.smoothStratum_nonempty [IsIntegral X]
    (f : X ⟶ Spec (.of K)) [LocallyOfFinitePresentation f] :
    Nonempty (CycleClass.Geometric.SmoothStratum.smoothStratum f) :=
  (CycleClass.Geometric.SmoothStratum.smoothStratum_denseRange f).nonempty

instance CycleClass.Geometric.SmoothStratum.smoothStratum_isIntegral [IsIntegral X]
    (f : X ⟶ Spec (.of K)) [LocallyOfFinitePresentation f] :
    IsIntegral (CycleClass.Geometric.SmoothStratum.smoothStratum f) :=
  AlgebraicGeometry.isIntegral_of_isOpenImmersion (CycleClass.Geometric.SmoothStratum.smoothStratumι f)

/-- The closure of the smooth stratum in the ambient scheme is exactly the
irreducible cycle support from which it was constructed. -/
theorem CycleClass.Geometric.SmoothStratum.reducedSupportSmoothStratum_closure_range (Z : IrreducibleCloseds X)
    (f : CycleClass.Geometric.GenericPoint.reducedSupportScheme Z ⟶ Spec (.of K)) [LocallyOfFinitePresentation f] :
    closure (Set.range (CycleClass.Geometric.SmoothStratum.reducedSupportSmoothStratumι Z f)) = (Z : Set X) := by
  change closure (Set.range ((CycleClass.Geometric.GenericPoint.reducedSupportι Z) ∘ (CycleClass.Geometric.SmoothStratum.smoothStratumι f))) = (Z : Set X)
  rw [Set.range_comp, (CycleClass.Geometric.GenericPoint.reducedSupportι Z).isClosedEmbedding.closure_image_eq,
    (CycleClass.Geometric.SmoothStratum.smoothStratum_denseRange f).closure_range, Set.image_univ, CycleClass.Geometric.GenericPoint.range_reducedSupportι]

/-- A point of the support omitted by its actual smooth stratum has ambient
codimension at least p+1. -/
theorem CycleClass.Geometric.SmoothStratum.reducedSupportSmoothStratum_complement_coheight (p : ℕ)
    (Z : Foundations.Scheme.CycleSupports.IrreducibleCycleSupport X p)
    (f : CycleClass.Geometric.GenericPoint.reducedSupportScheme Z.1 ⟶ Spec (.of K)) [LocallyOfFinitePresentation f]
    (y : X) (hy : y ∈ (Z.1 : Set X))
    (homit : y ∉ Set.range (CycleClass.Geometric.SmoothStratum.reducedSupportSmoothStratumι Z.1 f)) :
    ((p + 1 : ℕ) : ℕ∞) ≤ Order.coheight y := by
  have hyrange : y ∈ Set.range (CycleClass.Geometric.GenericPoint.reducedSupportι Z.1) := by
    simpa only [CycleClass.Geometric.GenericPoint.range_reducedSupportι] using hy
  obtain ⟨x, rfl⟩ := hyrange
  apply CycleClass.Geometric.SingularCodimension.reducedSupport_singular_ambient_coheight p Z f x
  change x ∉ f.smoothLocus
  intro hx
  apply homit
  exact ⟨⟨x, hx⟩, rfl⟩

/-- The smooth stratum of an actual cycle support in the given complex variety. -/
def Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation.cycleSupportSmoothStratum (P : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation) (p : ℕ)
    (Z : Foundations.Scheme.CycleSupports.IrreducibleCycleSupport P.carrier p) : Scheme :=
  CycleClass.Geometric.SmoothStratum.smoothStratum (CycleClass.Geometric.SupportFiniteType.supportStructureMap Z.1 P.structureMap)

/-- Its actual complex structure morphism. -/
def Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation.cycleSupportSmoothStratumToBase (P : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation) (p : ℕ)
    (Z : Foundations.Scheme.CycleSupports.IrreducibleCycleSupport P.carrier p) :
    P.cycleSupportSmoothStratum p Z ⟶ Foundations.Scheme.ProjectiveSpace.complexBase :=
  CycleClass.Geometric.SmoothStratum.smoothStratumToBase (CycleClass.Geometric.SupportFiniteType.supportStructureMap Z.1 P.structureMap)

instance Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation.cycleSupportSmoothStratumToBase_isSmooth (P : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation)
    (p : ℕ) (Z : Foundations.Scheme.CycleSupports.IrreducibleCycleSupport P.carrier p) :
    Smooth (P.cycleSupportSmoothStratumToBase p Z) :=
  inferInstanceAs (Smooth (CycleClass.Geometric.SmoothStratum.smoothStratumToBase (CycleClass.Geometric.SupportFiniteType.supportStructureMap Z.1 P.structureMap)))

/-- The smooth locally closed stratum is dense in the actual cycle support. -/
theorem Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation.cycleSupportSmoothStratum_closure_range (P : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation)
    (p : ℕ) (Z : Foundations.Scheme.CycleSupports.IrreducibleCycleSupport P.carrier p) :
    closure (Set.range (CycleClass.Geometric.SmoothStratum.reducedSupportSmoothStratumι Z.1
      (CycleClass.Geometric.SupportFiniteType.supportStructureMap Z.1 P.structureMap))) = (Z.1 : Set P.carrier) :=
  CycleClass.Geometric.SmoothStratum.reducedSupportSmoothStratum_closure_range Z.1 (CycleClass.Geometric.SupportFiniteType.supportStructureMap Z.1 P.structureMap)

/-- The omitted part of an actual cycle support has larger ambient codimension. -/
theorem Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation.cycleSupportSmoothStratum_complement_coheight (P : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation)
    (p : ℕ) (Z : Foundations.Scheme.CycleSupports.IrreducibleCycleSupport P.carrier p)
    (y : P.carrier) (hy : y ∈ (Z.1 : Set P.carrier))
    (homit : y ∉ Set.range (CycleClass.Geometric.SmoothStratum.reducedSupportSmoothStratumι Z.1
      (CycleClass.Geometric.SupportFiniteType.supportStructureMap Z.1 P.structureMap))) :
    ((p + 1 : ℕ) : ℕ∞) ≤ Order.coheight y :=
  CycleClass.Geometric.SmoothStratum.reducedSupportSmoothStratum_complement_coheight p Z
    (CycleClass.Geometric.SupportFiniteType.supportStructureMap Z.1 P.structureMap) y hy homit

end

end OAI.AlgebraicGeometry

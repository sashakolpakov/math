import OAI.AlgebraicGeometry.CycleClass.Thom.Affine.SectionFunction
import OAI.AlgebraicGeometry.CycleClass.Thom.SupportSectionGerm
import OAI.AlgebraicGeometry.CycleClass.Thom.Scheme.RegularOrder
import OAI.AlgebraicGeometry.CycleClass.Thom.Cycle.MeetingOpen
import OAI.AlgebraicGeometry.CycleClass.Thom.Intersection.Supports

/-! # Closed Support -/

namespace OAI

noncomputable section

namespace AlgebraicGeometry.CycleClass.Thom.Section.ClosedSupport.Constructions.Principal

/-! The actual principal cycle of an ambient regular section is supported
on the parent cycle and the section's zero set, including the omitted
higher-codimension boundary. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace

open OAI.AlgebraicGeometry.CycleClass.Thom.Affine.SectionFunction.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.SupportSectionGerm.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.SupportStalkModule.Constructions
open OAI.AlgebraicGeometry.CycleClass.Thom.Normalization.GoodSmoothMap.Constructions.AffineOpen OAI.AlgebraicGeometry.CycleClass.Thom.Normalization.AmbientMap.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.Scheme.RegularOrder.Constructions
open OAI.AlgebraicGeometry.CycleClass.Thom.Intersection.Supports OAI.AlgebraicGeometry.CycleClass.Thom.Cycle.MeetingOpen.Constructions

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

 theorem ord_algebraMap_stalk_unit (X : Scheme) [IsIntegral X] [IsLocallyNoetherian X]
    (x : X) (s : X.presheaf.stalk x) (hs : IsUnit s) :
    X.ord (algebraMap (X.presheaf.stalk x) X.functionField s) x = 0 := by
  by_cases hx : Order.coheight x = 1
  · rw [Thom.Scheme.RegularOrder.Constructions.ord_algebraMap_stalk X x hx s hs.ne_zero, Ring.ord_of_isUnit hs]
    rfl
  · exact Scheme.ord_eq_zero_of_coheight_neq_one hx _

variable {V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety} {p : ℕ} (D : Geometric.DimensionCycles.DimensionCycleSupport V p)
  (B : V.carrier.Opens) [Nonempty ((Normalization.AmbientMap.Constructions.normalizationToAmbient V D.val).left ⁻¹ᵁ B)]
  (s : Γ((Normalization.GoodSmoothMap.Constructions.AffineOpen.affineBase B).left, ⊤)) (C : IrreducibleCloseds V.carrier)

 theorem principalCoefficient_support
    (hc : IntersectionGeometry.principalDivisorCoefficient V.presentation D.val (Affine.SectionFunction.Constructions.parentSectionFunction D B s) C ≠ 0) :
    (C : Set V.carrier) ⊆ D.val ∧
      ∀ x : V.carrier, x ∈ (C : Set V.carrier) → x ∉ V.carrier.basicOpen (B.topIso.hom s) := by
  classical
  have hD : IntersectionGeometry.supportPoint C ∈ (D.val : Set V.carrier) := by
    by_contra hn
    exact hc (by simp only [IntersectionGeometry.principalDivisorCoefficient, dite_eq_right hn])
  refine ⟨(Intersection.Supports.supportPoint_mem_iff_subset ⟨(D.val : Set V.carrier), D.val.isClosed⟩ C).mp hD, ?_⟩
  intro x hx hunit
  have hu := Cycle.MeetingOpen.Constructions.supportPoint_mem_of_meets C (V.carrier.basicOpen (B.topIso.hom s)) x hx hunit
  have hb : IntersectionGeometry.supportPoint C ∈ B := V.carrier.basicOpen_le (B.topIso.hom s) hu
  let : Nonempty (D.inclusion ⁻¹ᵁ B) :=
    ⟨⟨IntersectionGeometry.supportPreimage D.val (IntersectionGeometry.supportPoint C) hD, SupportSectionGerm.Constructions.supportPreimage_mem_open V.carrier D.val (IntersectionGeometry.supportPoint C) hD B hb⟩⟩
  have hg := SupportSectionGerm.Constructions.restrictedFunction_eq_supportStalk_germ V.carrier D.val (IntersectionGeometry.supportPoint C) hD B hb (B.topIso.hom s)
  have hgu : IsUnit (V.carrier.presheaf.germ B (IntersectionGeometry.supportPoint C) hb (B.topIso.hom s)) :=
    (V.carrier.mem_basicOpen (B.topIso.hom s) (IntersectionGeometry.supportPoint C) hb).mp hu
  have hsu := (SupportStalkModule.Constructions.supportStalkMap V.carrier D.val (IntersectionGeometry.supportPoint C) hD).hom.isUnit_map hgu
  apply hc
  rw [IntersectionGeometry.principalDivisorCoefficient, dite_eq_left hD]
  change (D.scheme.ord (Affine.SectionFunction.Constructions.parentSectionFunction D B s) (IntersectionGeometry.supportPreimage D.val (IntersectionGeometry.supportPoint C) hD) : ℚ) = 0
  change Affine.SectionFunction.Constructions.parentSectionFunction D B s = _ at hg
  rw [hg, ord_algebraMap_stalk_unit D.scheme _ _ hsu, Int.cast_zero]

end AlgebraicGeometry.CycleClass.Thom.Section.ClosedSupport.Constructions.Principal

namespace AlgebraicGeometry.CycleClass.Thom.Section.ClosedSupport.Constructions

/-! A regular section on an ambient open gives a genuine global closed
support of codimension at least one more than its parent cycle. Its
principal cycle is contained in that closed support. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace

open OAI.AlgebraicGeometry.CycleClass.Thom.Affine.SectionFunction.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.Normalization.GoodSmoothMap.Constructions.AffineOpen OAI.AlgebraicGeometry.CycleClass.Thom.Normalization.AmbientMap.Constructions
open OAI.AlgebraicGeometry.CycleClass.Thom.Normalization.Scheme.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.Section.ClosedSupport.Constructions.Principal

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety} {p : ℕ} (D : Geometric.DimensionCycles.DimensionCycleSupport V p)
  (B : V.carrier.Opens) (s : Γ((Normalization.GoodSmoothMap.Constructions.AffineOpen.affineBase B).left, ⊤))

def sectionClosedSupport : Closeds V.carrier :=
  ⟨(D.val : Set V.carrier) ∩ (V.carrier.basicOpen (B.topIso.hom s) : Set V.carrier)ᶜ,
    D.val.isClosed.inter (V.carrier.basicOpen (B.topIso.hom s)).isOpen.isClosed_compl⟩

variable [Nonempty ((Normalization.AmbientMap.Constructions.normalizationToAmbient V D.val).left ⁻¹ᵁ B)]

local instance : Nonempty (D.inclusion ⁻¹ᵁ B) := by
  obtain ⟨x⟩ := ‹Nonempty ((normalizationToAmbient V D.val).left ⁻¹ᵁ B)›
  exact ⟨⟨Normalization.Scheme.Constructions.normalizationMap D.scheme x.val, x.property⟩⟩

variable (hs : Affine.SectionFunction.Constructions.parentSectionFunction D B s ≠ 0)

include hs in
theorem parent_genericPoint_mem_unitOpen : IntersectionGeometry.supportPoint D.val ∈ V.carrier.basicOpen (B.topIso.hom s) := by
  have hη : genericPoint D.scheme ∈ D.inclusion ⁻¹ᵁ B :=
    ((genericPoint_spec D.scheme).mem_open_set_iff (D.inclusion ⁻¹ᵁ B).isOpen).mpr
      (by simpa using (show Nonempty (D.inclusion ⁻¹ᵁ B) from inferInstance))
  have hu : genericPoint D.scheme ∈ D.scheme.basicOpen (D.inclusion.app B (B.topIso.hom s)) := by
    rw [D.scheme.mem_basicOpen _ _ hη]
    exact isUnit_iff_ne_zero.mpr hs
  have hp : D.inclusion (genericPoint D.scheme) ∈ V.carrier.basicOpen (B.topIso.hom s) := by
    change genericPoint D.scheme ∈ D.inclusion ⁻¹ᵁ V.carrier.basicOpen (B.topIso.hom s)
    rw [Scheme.preimage_basicOpen]
    exact hu
  exact (congrArg (fun x : V.carrier => x ∈ V.carrier.basicOpen (B.topIso.hom s))
    (Geometric.GenericPoint.reducedSupport_genericPoint_eq D.val)).mp hp

include hs in
theorem sectionClosedSupport_dimension (Z : IrreducibleCloseds V.carrier)
    (hZ : (Z : Set V.carrier) ⊆ sectionClosedSupport D B s) :
    Foundations.Scheme.SupportDimension.supportTranscendenceDimension Z V.structureMap + (Geometric.DimensionCycles.dimensionCodimension V D.val + 1) ≤
      Foundations.Scheme.TranscendenceDimension.schemeTranscendenceDimension V.structureMap := by
  have hle : Z ≤ D.val := fun _ hx => (hZ hx).1
  have hne : Z ≠ D.val := by
    intro he
    have hη : IntersectionGeometry.supportPoint D.val ∈ (D.val : Set V.carrier) :=
      (D.val.isIrreducible.isGenericPoint_genericPoint D.val.isClosed).mem
    have hηZ : IntersectionGeometry.supportPoint D.val ∈ (Z : Set V.carrier) :=
      (congrArg (fun C : IrreducibleCloseds V.carrier => IntersectionGeometry.supportPoint D.val ∈ (C : Set V.carrier)) he).mpr hη
    have hz := hZ hηZ
    exact hz.2 (parent_genericPoint_mem_unitOpen D B s hs)
  have hdim := Foundations.Scheme.SupportDimensionDrop.supportTranscendenceDimension_strictMono V.structureMap (lt_of_le_of_ne hle hne)
  change Foundations.Scheme.SupportDimension.supportTranscendenceDimension Z V.structureMap <
    Foundations.Scheme.SupportDimension.supportTranscendenceDimension D.val V.structureMap at hdim
  have hD := Geometric.DimensionCycles.supportDimension_add_dimensionCodimension V D.val
  omega

omit hs in
theorem principalCoefficient_subset_sectionClosedSupport (C : IrreducibleCloseds V.carrier)
    (hc : IntersectionGeometry.principalDivisorCoefficient V.presentation D.val (Affine.SectionFunction.Constructions.parentSectionFunction D B s) C ≠ 0) :
    (C : Set V.carrier) ⊆ sectionClosedSupport D B s := by
  obtain ⟨hD, hu⟩ := Principal.principalCoefficient_support D B s C hc
  exact fun x hx => ⟨hD hx, hu x hx⟩

end AlgebraicGeometry.CycleClass.Thom.Section.ClosedSupport.Constructions

end

end OAI

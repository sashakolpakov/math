import OAI.AlgebraicGeometry.CycleClass.Thom.Supported.Map

/-! # Projective Support Isolation -/

namespace OAI

noncomputable section

namespace AlgebraicGeometry.CycleClass.Thom.Supported.ProjectiveSupportIsolation

/-! The genuine Serre intersection coefficients define a finite cycle
supported on the original algebraic intersection. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

namespace Constructions.Intersection

open OAI.AlgebraicGeometry.CycleClass.Thom.Supported.Map.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.Scheme.SupportDetection.Constructions.Neighborhoods OAI.AlgebraicGeometry.CycleClass.Thom.Scheme.MinimalSupport.Constructions

theorem supportedSupport_finite (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety) (F : Closeds V.carrier) (c : ℕ)
    (hc : ∀ Z : IrreducibleCloseds V.carrier, (Z : Set V.carrier) ⊆ F → c ≤ Geometric.DimensionCycles.dimensionCodimension V Z) :
    Finite (Map.Constructions.SupportedSupport V F c) := by
  let : IsIntegral V.toOver.left := inferInstanceAs (IsIntegral V.carrier)
  let : Smooth V.toOver.hom := inferInstanceAs (Smooth V.structureMap)
  let : AlgebraicGeometry.IsNoetherian V.toOver.left :=
    inferInstanceAs (AlgebraicGeometry.IsNoetherian V.carrier)
  have hd (Z : IrreducibleCloseds V.carrier) (hZ : (Z : Set V.carrier) ⊆ F) :
      Foundations.Scheme.SupportDimension.supportTranscendenceDimension Z V.structureMap + c ≤ Foundations.Scheme.TranscendenceDimension.schemeTranscendenceDimension V.structureMap := by
    have h := hc Z hZ
    have he := Geometric.DimensionCycles.supportDimension_add_dimensionCodimension V Z
    omega
  let : Finite (Scheme.SupportDetection.Constructions.Neighborhoods.MinimalSupport V.toOver F c) := Scheme.MinimalSupport.Constructions.minimalSupport_finite V.toOver F c hd
  let j : Map.Constructions.SupportedSupport V F c → Scheme.SupportDetection.Constructions.Neighborhoods.MinimalSupport V.toOver F c := fun Z =>
    ⟨Z.val.val, Z.property, by
      have h := Geometric.DimensionCycles.supportDimension_add_dimensionCodimension V Z.val.val
      rw [Z.val.property] at h
      exact h⟩
  apply Finite.of_injective j
  intro A B h
  apply Subtype.ext
  apply Subtype.ext
  exact congrArg (fun Z : Scheme.SupportDetection.Constructions.Neighborhoods.MinimalSupport V.toOver F c => Z.val) h

variable (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety) (p q : ℕ)
  (A : Geometric.DimensionCycles.DimensionCycleSupport V p) (B : Geometric.DimensionCycles.DimensionCycleSupport V q)

def intersectionClosed : Closeds V.carrier :=
  ⟨(A.val : Set V.carrier) ∩ (B.val : Set V.carrier), A.val.isClosed.inter B.val.isClosed⟩

variable (hproper : ∀ Z : IrreducibleCloseds V.carrier,
  (Z : Set V.carrier) ⊆ intersectionClosed V p q A B → p + q ≤ Geometric.DimensionCycles.dimensionCodimension V Z)

def supportedPairCycle : Map.Constructions.SupportedCycle V (intersectionClosed V p q A B) (p + q) := by
  let : Finite (Map.Constructions.SupportedSupport V (intersectionClosed V p q A B) (p + q)) :=
    supportedSupport_finite V _ (p + q) hproper
  exact Finsupp.ofSupportFinite
    (fun Z => IntersectionGeometry.intersectionMultiplicity V.presentation A.val B.val Z.val.val) (Set.toFinite _)

theorem supportedPairCycle_apply (Z : Map.Constructions.SupportedSupport V (intersectionClosed V p q A B) (p + q)) :
    supportedPairCycle V p q A B hproper Z =
      IntersectionGeometry.intersectionMultiplicity V.presentation A.val B.val Z.val.val := rfl

theorem supportedPairCycle_forget_coefficient (C : Geometric.DimensionCycles.DimensionCycleSupport V (p + q)) :
    Map.Constructions.forgetCycle V (intersectionClosed V p q A B) (p + q) (supportedPairCycle V p q A B hproper) C =
      IntersectionGeometry.intersectionMultiplicity V.presentation A.val B.val C.val := by
  classical
  by_cases hC : (C.val : Set V.carrier) ⊆ intersectionClosed V p q A B
  · exact (Finsupp.mapDomain_apply_of_injective Subtype.val_injective
      (supportedPairCycle V p q A B hproper) ⟨C, hC⟩).trans
      (supportedPairCycle_apply V p q A B hproper ⟨C, hC⟩)
  · have hm : IntersectionGeometry.intersectionMultiplicity V.presentation A.val B.val C.val = 0 := by
      apply dite_eq_right
      intro h
      exact hC ((Intersection.Supports.supportPoint_mem_iff_subset
        (intersectionClosed V p q A B) C.val).mp h)
    rw [hm]
    apply Finsupp.mapDomain_of_notMem_range
    rintro ⟨Z, hZ⟩
    exact hC (hZ ▸ Z.property)

end Constructions.Intersection

end AlgebraicGeometry.CycleClass.Thom.Supported.ProjectiveSupportIsolation

namespace AlgebraicGeometry.CycleClass.Thom.Supported.ProjectiveSupportIsolation.Constructions

/-! The actual minimum-codimension supports used by cohomology
detection agree with the supports of the original finite cycle. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace

open OAI.AlgebraicGeometry.CycleClass.Thom.Supported.Map.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.Scheme.SupportDetection.Constructions.Neighborhoods OAI.AlgebraicGeometry.CycleClass.Thom.Scheme.MinimalSupport.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.Scheme.MinimalSupport.Constructions.Isolation

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety) (F : Closeds V.carrier) (c : ℕ)

local instance : IsIntegral V.toOver.left := V.property
local instance : Smooth V.toOver.hom := V.presentation.smooth
local instance : AlgebraicGeometry.IsNoetherian V.toOver.left := inferInstanceAs (AlgebraicGeometry.IsNoetherian V.carrier)

def minimalCycleSupport (Z : Scheme.SupportDetection.Constructions.Neighborhoods.MinimalSupport V.toOver F c) : Geometric.DimensionCycles.DimensionCycleSupport V c :=
  ⟨Z.val, by
    have h := Geometric.DimensionCycles.supportDimension_add_dimensionCodimension V Z.val
    have hZ := Z.property.2
    change Foundations.Scheme.SupportDimension.supportTranscendenceDimension Z.val V.structureMap + c = Foundations.Scheme.TranscendenceDimension.schemeTranscendenceDimension V.structureMap at hZ
    omega⟩

def minimalSupportedSupport (Z : Scheme.SupportDetection.Constructions.Neighborhoods.MinimalSupport V.toOver F c) : Map.Constructions.SupportedSupport V F c :=
  ⟨minimalCycleSupport V F c Z, Z.property.1⟩

def supportedMinimalSupport (Z : Map.Constructions.SupportedSupport V F c) : Scheme.SupportDetection.Constructions.Neighborhoods.MinimalSupport V.toOver F c :=
  ⟨Z.val.val, Z.property, by
    have h := Geometric.DimensionCycles.supportDimension_add_dimensionCodimension V Z.val.val
    rw [Z.val.property] at h
    exact h⟩

variable (hc : ∀ Z : IrreducibleCloseds V.carrier, (Z : Set V.carrier) ⊆ F → c ≤ Geometric.DimensionCycles.dimensionCodimension V Z)

include hc in
theorem support_dimension_bound (Z : IrreducibleCloseds V.carrier) (hZ : (Z : Set V.carrier) ⊆ F) :
    Foundations.Scheme.SupportDimension.supportTranscendenceDimension Z V.toOver.hom + c ≤ Foundations.Scheme.TranscendenceDimension.schemeTranscendenceDimension V.toOver.hom := by
  have h := hc Z hZ
  have he := Geometric.DimensionCycles.supportDimension_add_dimensionCodimension V Z
  change Foundations.Scheme.SupportDimension.supportTranscendenceDimension Z V.structureMap + c ≤ Foundations.Scheme.TranscendenceDimension.schemeTranscendenceDimension V.structureMap
  omega

include hc in
theorem isolatingOpen_avoids_other (Z : Scheme.SupportDetection.Constructions.Neighborhoods.MinimalSupport V.toOver F c) (W : Map.Constructions.SupportedSupport V F c)
    (hW : W ≠ minimalSupportedSupport V F c Z) :
    (Scheme.MinimalSupport.Constructions.Isolation.isolatingOpen V.toOver F c Z : Set V.toOver.left) ⊆ (W.val.val : Set V.carrier)ᶜ := by
  obtain ⟨D, hD⟩ := Scheme.MinimalSupport.Constructions.minimalSupport_eq_component V.toOver F c (support_dimension_bound V F c hc)
    (supportedMinimalSupport V F c W)
  have hn : IntersectionGeometry.closedComponentSupport V.carrier F D ≠ Z.val := by
    intro he
    apply hW
    apply Subtype.ext
    apply Subtype.ext
    exact hD.symm.trans he
  intro x hx hxW
  exact hx.1 (Set.mem_iUnion.mpr ⟨⟨D, hn⟩, hD.symm ▸ hxW⟩)

end AlgebraicGeometry.CycleClass.Thom.Supported.ProjectiveSupportIsolation.Constructions

end

end OAI

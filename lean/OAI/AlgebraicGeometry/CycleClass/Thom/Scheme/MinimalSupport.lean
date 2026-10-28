import OAI.AlgebraicGeometry.CycleClass.Thom.Scheme.SupportDetection
import OAI.AlgebraicGeometry.CycleClass.Thom.Intersection.Supports

/-! # Minimal Support -/

namespace OAI.AlgebraicGeometry.CycleClass.Thom.Scheme.MinimalSupport

noncomputable section

section

/-! The supports used by the local detection theorem form a finite family
of genuine irreducible components of the original algebraic closed set. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace
set_option backward.isDefEq.respectTransparency false

namespace Constructions

open OAI.AlgebraicGeometry.CycleClass.Thom.Scheme.SupportDetection.Constructions.Neighborhoods

variable (X : Over Foundations.Scheme.ProjectiveSpace.complexBase) [IsIntegral X.left] [Smooth X.hom]
  [AlgebraicGeometry.IsNoetherian X.left] (F : Closeds X.left) (c : ℕ)
  (hc : ∀ Z : IrreducibleCloseds X.left, (Z : Set X.left) ⊆ F →
    Foundations.Scheme.SupportDimension.supportTranscendenceDimension Z X.hom + c ≤ Foundations.Scheme.TranscendenceDimension.schemeTranscendenceDimension X.hom)

include hc in
omit [AlgebraicGeometry.IsNoetherian X.left] in
theorem minimalSupport_eq_of_le (Z : SupportDetection.Constructions.Neighborhoods.MinimalSupport X F c)
    (W : IrreducibleCloseds X.left) (hW : (W : Set X.left) ⊆ F) (hZW : Z.val ≤ W) : Z.val = W := by
  by_contra hn
  have ht := Foundations.Scheme.SupportDimensionDrop.supportTranscendenceDimension_strictMono X.hom (lt_of_le_of_ne hZW hn)
  change Foundations.Scheme.SupportDimension.supportTranscendenceDimension Z.val X.hom < Foundations.Scheme.SupportDimension.supportTranscendenceDimension W X.hom at ht
  have hd := hc W hW
  have hz := Z.property.2
  omega

include hc in
omit [AlgebraicGeometry.IsNoetherian X.left] in
theorem minimalSupport_eq_component (Z : SupportDetection.Constructions.Neighborhoods.MinimalSupport X F c) :
    ∃ D : irreducibleComponents F, IntersectionGeometry.closedComponentSupport X.left F D = Z.val := by
  obtain ⟨D, hD⟩ := Intersection.Supports.closedComponentSupport_covers X.left F Z.val Z.property.1
  exact ⟨D, (minimalSupport_eq_of_le X F c hc Z _
    (Intersection.Supports.closedComponentSupport_subset X.left F D) hD).symm⟩

include hc in
theorem minimalSupport_finite : Finite (SupportDetection.Constructions.Neighborhoods.MinimalSupport X F c) := by
  let : NoetherianSpace F := NoetherianSpace.set (F : Set X.left)
  let : Finite (irreducibleComponents F) :=
    (NoetherianSpace.finite_irreducibleComponents (α := F)).to_subtype
  let f : SupportDetection.Constructions.Neighborhoods.MinimalSupport X F c → irreducibleComponents F :=
    fun Z => Classical.choose (minimalSupport_eq_component X F c hc Z)
  have hf : Function.Injective f := by
    intro A B hAB
    apply Subtype.ext
    exact (Classical.choose_spec (minimalSupport_eq_component X F c hc A)).symm.trans
      ((congrArg (IntersectionGeometry.closedComponentSupport X.left F) hAB).trans
        (Classical.choose_spec (minimalSupport_eq_component X F c hc B)))
  exact Finite.of_injective f hf

end Constructions

end

/-! Each minimum-codimension component has an actual algebraic neighborhood
where the closed support is that component and its singular boundary is absent. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace
set_option backward.isDefEq.respectTransparency false

namespace Constructions.Isolation

open OAI.AlgebraicGeometry.CycleClass.Thom.Scheme.SupportDetection.Constructions.Neighborhoods OAI.AlgebraicGeometry.CycleClass.Thom.Scheme.MinimalSupport.Constructions

variable (X : Over Foundations.Scheme.ProjectiveSpace.complexBase) [IsIntegral X.left] [Smooth X.hom]
  [AlgebraicGeometry.IsNoetherian X.left] (F : Closeds X.left) (c : ℕ)
  (Z : SupportDetection.Constructions.Neighborhoods.MinimalSupport X F c)

local instance : Finite (irreducibleComponents F) := by
  let : NoetherianSpace F := NoetherianSpace.set (F : Set X.left)
  exact (NoetherianSpace.finite_irreducibleComponents (α := F)).to_subtype

def otherComponentsClosed : Closeds X.left :=
  ⟨⋃ D : {D : irreducibleComponents F // IntersectionGeometry.closedComponentSupport X.left F D ≠ Z.val},
    (IntersectionGeometry.closedComponentSupport X.left F D.val : Set X.left),
    isClosed_iUnion_of_finite (fun D => (IntersectionGeometry.closedComponentSupport X.left F D.val).isClosed)⟩

def isolatingOpen : X.left.Opens :=
  (otherComponentsClosed X F c Z).compl ⊓
    ⟨(Geometric.StratumDimension.supportSingularBoundary Z.val X.hom)ᶜ,
      (Geometric.StratumDimension.isClosed_supportSingularBoundary Z.val X.hom).isOpen_compl⟩

variable (hc : ∀ W : IrreducibleCloseds X.left, (W : Set X.left) ⊆ F →
    Foundations.Scheme.SupportDimension.supportTranscendenceDimension W X.hom + c ≤ Foundations.Scheme.TranscendenceDimension.schemeTranscendenceDimension X.hom)

include hc in
theorem genericPoint_mem_isolatingOpen : irreducibleSetEquivPoints Z.val ∈ isolatingOpen X F c Z := by
  refine ⟨?_, Geometric.StratumDimension.genericPoint_not_mem_supportSingularBoundary Z.val X.hom⟩
  intro hx
  obtain ⟨D, hD⟩ := Set.mem_iUnion.mp hx
  have hzD : Z.val ≤ IntersectionGeometry.closedComponentSupport X.left F D.val :=
    (Intersection.Supports.supportPoint_mem_iff_subset
      ⟨_, (IntersectionGeometry.closedComponentSupport X.left F D.val).isClosed⟩ Z.val).mp hD
  exact D.property (minimalSupport_eq_of_le X F c hc Z _
    (Intersection.Supports.closedComponentSupport_subset X.left F D.val) hzD).symm

omit [Smooth X.hom] in
theorem mem_component_of_avoids_others (x : X.left)
    (hx : x ∈ F) (ho : x ∉ otherComponentsClosed X F c Z) : x ∈ (Z.val : Set X.left) := by
  classical
  let W : IrreducibleCloseds X.left := irreducibleSetEquivPoints.symm x
  have hWF : (W : Set X.left) ⊆ F :=
    F.isClosed.closure_subset_iff.mpr (Set.singleton_subset_iff.mpr hx)
  obtain ⟨D, hD⟩ := Intersection.Supports.closedComponentSupport_covers X.left F W hWF
  have hxW : x ∈ (W : Set X.left) := subset_closure (Set.mem_singleton x)
  have he : IntersectionGeometry.closedComponentSupport X.left F D = Z.val := by
    by_contra hn
    exact ho (Set.mem_iUnion.mpr ⟨⟨D, hn⟩, hD hxW⟩)
  exact he ▸ hD hxW

theorem isolatingOpen_support (x : X.left) (hx : x ∈ isolatingOpen X F c Z) :
    x ∈ F ↔ x ∈ (Z.val : Set X.left) :=
  ⟨fun h => mem_component_of_avoids_others X F c Z x h hx.1, fun h => Z.property.1 h⟩

theorem isolatingOpen_avoids_singularBoundary :
    (isolatingOpen X F c Z : Set X.left) ⊆ (Geometric.StratumDimension.supportSingularBoundary Z.val X.hom)ᶜ :=
  fun _ hx => hx.2

end Constructions.Isolation

end

end OAI.AlgebraicGeometry.CycleClass.Thom.Scheme.MinimalSupport

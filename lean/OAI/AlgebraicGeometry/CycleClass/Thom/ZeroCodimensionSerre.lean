import OAI.AlgebraicGeometry.CycleClass.Thom.CodimensionZeroSupport
import OAI.AlgebraicGeometry.CycleClass.Thom.SmoothSerreIntersection

/-! # Zero Codimension Serre -/

namespace OAI.AlgebraicGeometry.CycleClass.Thom.ZeroCodimensionSerre.Constructions

noncomputable section

/-! A codimension-zero support is the actual ambient integral scheme.
Its self-intersection has native Serre multiplicity one and the expected cup. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace
open RingTheory.Sequence

open OAI.AlgebraicGeometry.CycleClass.Thom.CodimensionZeroSupport.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.SupportStalkModule.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.Immersion.IntersectionCoordinates.Constructions
open OAI.AlgebraicGeometry.CycleClass.Thom.SmoothImmersion.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.Supported.ProjectiveSupportIsolation.Constructions.Intersection OAI.AlgebraicGeometry.CycleClass.Thom.Supported.Map.Constructions

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety) (A : Geometric.DimensionCycles.DimensionCycleSupport V 0)

theorem support_univ : (A.val : Set V.carrier) = Set.univ :=
  CodimensionZeroSupport.Constructions.integralSupport_eq_univ_of_codimension_zero V A.val A.property

instance inclusion_isIso : IsIso A.inclusion := by
  have hs : Function.Surjective A.inclusion := by
    apply Set.range_eq_univ.mp
    change Set.range (Geometric.GenericPoint.reducedSupportι A.val) = Set.univ
    rw [Geometric.GenericPoint.range_reducedSupportι, support_univ V A]
  let : AlgebraicGeometry.Surjective A.inclusion := ⟨hs⟩
  exact isIso_of_isClosedImmersion_of_surjective A.inclusion

instance support_smooth : Smooth A.structureMap := inferInstanceAs (Smooth (A.inclusion ≫ V.structureMap))

theorem supportStalk_kernel (x : V.carrier) (hx : x ∈ (A.val : Set V.carrier)) :
    RingHom.ker (SupportStalkModule.Constructions.supportStalkMap V.carrier A.val x hx).hom = ⊥ := by
  let : IsIso (Geometric.GenericPoint.reducedSupportι A.val) := inclusion_isIso V A
  let : IsIso (SupportStalkModule.Constructions.supportStalkMap V.carrier A.val x hx) := by unfold SupportStalkModule.Constructions.supportStalkMap; infer_instance
  exact (RingHom.injective_iff_ker_eq_bot _).mp
    (ConcreteCategory.bijective_of_isIso (SupportStalkModule.Constructions.supportStalkMap V.carrier A.val x hx)).1

theorem genericSupport_maximal (hx : IntersectionGeometry.supportPoint A.val ∈ (A.val : Set V.carrier)) :
    IsLocalRing.maximalIdeal (A.scheme.presheaf.stalk (IntersectionGeometry.supportPreimage A.val (IntersectionGeometry.supportPoint A.val) hx)) = ⊥ := by
  have he : IntersectionGeometry.supportPreimage A.val (IntersectionGeometry.supportPoint A.val) hx = genericPoint A.scheme :=
    (Geometric.GenericPoint.reducedSupportι A.val).isClosedEmbedding.injective
      ((IntersectionGeometry.supportPreimage_spec A.val (IntersectionGeometry.supportPoint A.val) hx).trans (Geometric.GenericPoint.reducedSupport_genericPoint_eq A.val).symm)
  rw [he]
  change IsLocalRing.maximalIdeal A.scheme.functionField = ⊥
  exact IsLocalRing.maximalIdeal_eq_bot

theorem zero_normalTransverse : Immersion.IntersectionCoordinates.Constructions.NormalTransverse (SmoothImmersion.Constructions.smoothCycleImmersion A) (SmoothImmersion.Constructions.smoothCycleImmersion A) := by
  intro x y h z
  refine ⟨0, ?_⟩
  funext i
  exact Fin.elim0 i

theorem geometricClass_selfSerre
    (hproper : ∀ Z : IrreducibleCloseds V.carrier,
      (Z : Set V.carrier) ⊆ Supported.ProjectiveSupportIsolation.Constructions.Intersection.intersectionClosed V 0 0 A A → 0 + 0 ≤ Geometric.DimensionCycles.dimensionCodimension V Z) :
    V.geometricCycleClassMap (0 + 0)
      (Supported.Map.Constructions.forgetCycle V (Supported.ProjectiveSupportIsolation.Constructions.Intersection.intersectionClosed V 0 0 A A) (0 + 0) (Supported.ProjectiveSupportIsolation.Constructions.Intersection.supportedPairCycle V 0 0 A A hproper)) =
    cast (congrArg (fun n => (V.rationalCohomology n : Type)) (add_add_add_comm 0 0 0 0))
      (AlgebraicTopology.Products.CupCohomology.singularCohomologyCup (R := ℚ) (Betti.Scheme.schemePointSpace V.toOver) (0 + 0) (0 + 0)
        A.geometricCycleClass A.geometricCycleClass) := by
  have hx : IntersectionGeometry.supportPoint A.val ∈ (A.val : Set V.carrier) :=
    (A.val.isIrreducible.isGenericPoint_genericPoint A.val.isClosed).mem
  exact SmoothSerreIntersection.Constructions.geometricClass_supportedSerreCycle A A A
    (Set.inter_self _).symm (zero_normalTransverse V A) hx hx []
    (by simpa using supportStalk_kernel V A (IntersectionGeometry.supportPoint A.val) hx)
    (by simp) (by simp)
    (by rw [genericSupport_maximal V A hx]; simp)

end

end OAI.AlgebraicGeometry.CycleClass.Thom.ZeroCodimensionSerre.Constructions

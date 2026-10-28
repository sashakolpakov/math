import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Stalk.DivisorSupport
import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Supports

/-! # Prime Component -/

namespace OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Local.PrimeComponent

noncomputable section

/-! A prime minimal in the localized support determines a genuine
global irreducible component of the closed support through the point. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace

open OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Stalk.DivisorSupport

theorem exists_component (Z : Scheme) (S : Closeds Z) (x : Z)
    (p : PrimeSpectrum (Z.presheaf.stalk x)) (hp : Z.fromSpecStalk x p ∈ S)
    (hminimal : ∀ q : PrimeSpectrum (Z.presheaf.stalk x), Z.fromSpecStalk x q ∈ S →
      q.asIdeal ≤ p.asIdeal → q = p) :
    ∃ D : irreducibleComponents S, CycleClass.Thom.IntersectionGeometry.closedComponentSupport Z S D = Stalk.DivisorSupport.primeClosure Z x p := by
  let C := Stalk.DivisorSupport.primeClosure Z x p
  have hCP : CycleClass.Thom.IntersectionGeometry.supportPoint C = Z.fromSpecStalk x p := Stalk.DivisorSupport.primeClosure_point Z x p
  have hCS : (C : Set Z) ⊆ S := by
    apply (Supports.supportPoint_mem_iff_subset S C).mp
    rwa [hCP]
  obtain ⟨D, hCD⟩ := Supports.closedComponentSupport_covers Z S C hCS
  let E := CycleClass.Thom.IntersectionGeometry.closedComponentSupport Z S D
  have hηC : CycleClass.Thom.IntersectionGeometry.supportPoint C ∈ (C : Set Z) :=
    (C.isIrreducible.isGenericPoint_genericPoint C.isClosed).mem
  have hηE : CycleClass.Thom.IntersectionGeometry.supportPoint E ∈ (E : Set Z) :=
    (E.isIrreducible.isGenericPoint_genericPoint E.isClosed).mem
  have hEC : CycleClass.Thom.IntersectionGeometry.supportPoint E ⤳ Z.fromSpecStalk x p := by
    rw [← hCP]
    exact (E.isIrreducible.isGenericPoint_genericPoint E.isClosed).specializes (hCD hηC)
  have hpx : Z.fromSpecStalk x p ⤳ x := by
    simpa only [Scheme.fromSpecStalk_closedPoint] using
      (IsLocalRing.specializes_closedPoint p).map (Z.fromSpecStalk x).continuous
  have hrange : CycleClass.Thom.IntersectionGeometry.supportPoint E ∈ Set.range (Z.fromSpecStalk x) := by
    rw [Scheme.range_fromSpecStalk]
    exact hEC.trans hpx
  obtain ⟨q, hq⟩ := hrange
  have hqS : Z.fromSpecStalk x q ∈ S := by
    rw [hq]
    exact Supports.closedComponentSupport_subset Z S D hηE
  have hqp : q.asIdeal ≤ p.asIdeal := by
    apply (PrimeSpectrum.le_iff_specializes _ _).mpr
    apply (Z.fromSpecStalk x).isEmbedding.isInducing.specializes_iff.mp
    rwa [hq]
  have heq := hminimal q hqS hqp
  refine ⟨D, ?_⟩
  apply irreducibleSetEquivPoints.injective
  change CycleClass.Thom.IntersectionGeometry.supportPoint E = CycleClass.Thom.IntersectionGeometry.supportPoint C
  exact hq.symm.trans ((congrArg (Z.fromSpecStalk x) heq).trans hCP.symm)

end

end OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Local.PrimeComponent

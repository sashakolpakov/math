import OAI.AlgebraicGeometry.CycleClass.Thom.Open.ClosedImmersionComposition
import OAI.AlgebraicGeometry.CycleClass.Thom.Immersion.SupportedThomSource

/-! # Composed Support -/

namespace OAI.AlgebraicGeometry.CycleClass.Thom.ComposedSupport.Constructions

noncomputable section

/-! The original supported Thom isomorphism of the outer immersion,
with support in the actual image of a second closed immersion. -/

open _root_.CategoryTheory _root_.TopologicalSpace

open OAI.AlgebraicGeometry.CycleClass.Thom.Closed.ComplexImmersion.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.Immersion.SupportedThomSource.Constructions.Construction OAI.AlgebraicGeometry.CycleClass.Thom.Open.ClosedImmersionComposition.Constructions.ComplexManifold OAI.AlgebraicGeometry.CycleClass.Thom.Open.ClosedImmersionComposition.Constructions

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {V : Closed.ComplexImmersion.Constructions.ComplexManifold} {p q : ℕ} (Z : Closed.ComplexImmersion.Constructions.ClosedComplexImmersion V p)
  (C : Closed.ComplexImmersion.Constructions.ClosedComplexImmersion (Open.ClosedImmersionComposition.Constructions.ComplexManifold.sourceManifold Z) q)

def composedComplement : Opens V.analyticSpace :=
  ⟨(Set.range (Open.ClosedImmersionComposition.Constructions.compose Z C).regularComplementInclusion)ᶜ,
    (Open.ClosedImmersionComposition.Constructions.compose Z C).closed.isClosed_range.isOpen_compl⟩

theorem composedSourceComplement :
    Z.regularComplementInclusion ⁻¹' (composedComplement Z C : Set V.analyticSpace) =
      (Set.range C.regularComplementInclusion)ᶜ := by
  ext x
  constructor
  · intro hx hC
    obtain ⟨z, hz⟩ := hC
    exact hx ⟨z, congrArg Z.regularComplementInclusion hz⟩
  · intro hx hD
    obtain ⟨z, hz⟩ := hD
    exact hx ⟨z, Z.closed.injective hz⟩

theorem composedTargetComplement :
    ((Z.regularThomComplementOpen ⊔ composedComplement Z C : Opens V.analyticSpace) : Set V.analyticSpace) =
      (Set.range (Open.ClosedImmersionComposition.Constructions.compose Z C).regularComplementInclusion)ᶜ := by
  apply Set.union_eq_right.mpr
  intro x hx hD
  obtain ⟨z, hz⟩ := hD
  exact hx ⟨C.regularComplementInclusion z, hz⟩

def composedThomGysinIso
    (a : AlgebraicTopology.Cohomology.Singular.Representatives.cochainCocycles (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCochains (ModuleCat.of ℚ ℚ)
      V.analyticSpace (Z.regularThomComplementOpen : Set V.analyticSpace)) (2 * p))
    (ha : AlgebraicTopology.Cohomology.Singular.Representatives.cochainClass _ (2 * p) a = Z.regularThomClass) :
    AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology (ModuleCat.of ℚ ℚ) Z.regularAnalyticSpace
      (Set.range C.regularComplementInclusion)ᶜ (2 * q) ≅
    AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology (ModuleCat.of ℚ ℚ) V.analyticSpace
      (Set.range (Open.ClosedImmersionComposition.Constructions.compose Z C).regularComplementInclusion)ᶜ (2 * (p + q)) :=
  (eqToIso (congrArg (fun A => AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology (ModuleCat.of ℚ ℚ)
    Z.regularAnalyticSpace A (2 * q)) (composedSourceComplement Z C))).symm ≪≫
    Immersion.SupportedThomSource.Constructions.Construction.regularSourceThomSupportedGlobalIso Z a ha (composedComplement Z C) (2 * q) ≪≫
    eqToIso (congrArg (fun n => AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology (ModuleCat.of ℚ ℚ) V.analyticSpace
      ((Z.regularThomComplementOpen ⊔ composedComplement Z C : Opens V.analyticSpace) : Set V.analyticSpace) n)
      (Nat.mul_add 2 p q).symm) ≪≫
    eqToIso (congrArg (fun A => AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology (ModuleCat.of ℚ ℚ) V.analyticSpace A
      (2 * (p + q))) (composedTargetComplement Z C))

end

end OAI.AlgebraicGeometry.CycleClass.Thom.ComposedSupport.Constructions

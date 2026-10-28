import OAI.AlgebraicGeometry.CycleClass.Thom.CompactFiberSlant
import OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.CompactExteriorCup

/-! # Point Projection -/

namespace OAI.AlgebraicGeometry.CycleClass.Thom.Supported.PointProjection.Constructions

noncomputable section

/-! A product with a canonical fiber point projects to its original base class. -/

open _root_.CategoryTheory OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.CompactExteriorCup.Constructions
open scoped _root_.Manifold

open OAI.AlgebraicGeometry.CycleClass.Thom.CompactFiberSlant.Constructions.SupportedProjection OAI.AlgebraicGeometry.CycleClass.Thom.CompactFiberSlant.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.CompactPointIntegration.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.CanonicalLocalDual.Constructions

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

theorem productComplementMapsTo (X Y : TopCat.{0}) (S : Set X) (K : Set Y) :
    Set.MapsTo (𝟙 (TopCat.of (X × Y))) (S ×ˢ K)ᶜ (HodgeConjecture.DegreeTwo.RelativeCrossSupport.Constructions.crossSupportComplement X Y Sᶜ Kᶜ) := by
  intro z hz
  change z.1 ∉ S ∨ z.2 ∉ K
  change ¬ (z.1 ∈ S ∧ z.2 ∈ K) at hz
  tauto

variable (d : ℕ) {M : Type} [TopologicalSpace M] [T2Space M]
  [ChartedSpace (Fin d → ℂ) M] [IsManifold 𝓘(ℂ, Fin d → ℂ) 1 M]

def productPointClass (X : TopCat.{0}) (S : Set X) (hS : IsClosed S) (x : M) (p : ℕ)
    (a : AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology (ModuleCat.of ℚ ℚ) X Sᶜ p) :
    AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology (ModuleCat.of ℚ ℚ) (TopCat.of (X × M))
      (S ×ˢ {x})ᶜ (p + 2 * d) :=
  AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomologyMap (ModuleCat.of ℚ ℚ) (𝟙 (TopCat.of (X × M)))
    (productComplementMapsTo X (TopCat.of M) S {x}) (p + 2 * d)
    (HodgeConjecture.DegreeTwo.ExteriorCupSmallEvaluation.Constructions.relativeExteriorCup X (TopCat.of M) Sᶜ ({x}ᶜ) hS.isOpen_compl isClosed_singleton.isOpen_compl
      p (2 * d) a (CanonicalLocalDual.Constructions.canonicalLocalDual d x))

theorem projectSupported_point (X : TopCat.{0}) (S : Set X) (hS : IsClosed S)
    (K : Set M) (hK : IsCompact K) (x : M) (hx : x ∈ K) (p : ℕ)
    (a : AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology (ModuleCat.of ℚ ℚ) X Sᶜ p) :
    CompactFiberSlant.Constructions.SupportedProjection.projectSupported d X S K hK (S ×ˢ {x})
      (fun _ hz => ⟨hz.1, (Set.mem_singleton_iff.mp hz.2).symm ▸ hx⟩) p
      (productPointClass d X S hS x p a) = a := by
  have hp : Kᶜ ⊆ ({x}ᶜ : Set M) := fun y hy h => hy ((Set.mem_singleton_iff.mp h).symm ▸ hx)
  have he := HodgeConjecture.DegreeTwo.CompactExteriorCup.Constructions.relativeExteriorCup_support_naturality X (TopCat.of M)
    (A := Sᶜ) (A' := Sᶜ) (B := {x}ᶜ) (B' := Kᶜ) (fun _ hz => hz) hp
    hS.isOpen_compl isClosed_singleton.isOpen_compl hS.isOpen_compl hK.isClosed.isOpen_compl
    p (2 * d) a (CanonicalLocalDual.Constructions.canonicalLocalDual d x)
  simp only [AlgebraicTopology.Cohomology.Singular.RelativeOpenSupport.relativeSingularCohomologyMap_id, CategoryTheory.id_apply] at he
  have hc := ConcreteCategory.congr_hom
    (AlgebraicTopology.Cohomology.Singular.RelativeOpenSupport.relativeSingularCohomologyMap_comp (ModuleCat.of ℚ ℚ)
      (𝟙 (TopCat.of (X × M))) (𝟙 (TopCat.of (X × M)))
      (CompactFiberSlant.Constructions.SupportedProjection.boundedComplementMapsTo X S K (S ×ˢ {x})
        (fun _ hz => ⟨hz.1, (Set.mem_singleton_iff.mp hz.2).symm ▸ hx⟩))
      (productComplementMapsTo X (TopCat.of M) S {x}) (p + 2 * d))
    (HodgeConjecture.DegreeTwo.ExteriorCupSmallEvaluation.Constructions.relativeExteriorCup X (TopCat.of M) Sᶜ ({x}ᶜ) hS.isOpen_compl isClosed_singleton.isOpen_compl
      p (2 * d) a (CanonicalLocalDual.Constructions.canonicalLocalDual d x))
  refine (congrArg (CompactFiberSlant.Constructions.integrate d X Sᶜ K hK p) hc).trans ?_
  refine (congrArg (CompactFiberSlant.Constructions.integrate d X Sᶜ K hK p) he).symm.trans ?_
  exact CompactPointIntegration.Constructions.slant_compactPoint d X Sᶜ hS.isOpen_compl p K hK x hx a

end

end OAI.AlgebraicGeometry.CycleClass.Thom.Supported.PointProjection.Constructions

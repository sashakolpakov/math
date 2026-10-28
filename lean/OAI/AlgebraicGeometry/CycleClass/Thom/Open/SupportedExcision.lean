import OAI.AlgebraicGeometry.CycleClass.Thom.Open.NormalPairRestriction
import OAI.AlgebraicGeometry.CycleClass.Thom.ExteriorImageCup
import OAI.AlgebraicGeometry.CycleClass.Geometric.RelativeCohomologyExcision

/-! # Supported Excision -/

namespace OAI.AlgebraicGeometry.CycleClass.Thom.Open.SupportedExcision.Constructions

noncomputable section

/-! Excision is injective for the actual pair map of an immersion into an
open set containing its entire closed ambient image. -/

open _root_.CategoryTheory _root_.TopologicalSpace OAI.AlgebraicGeometry.CycleClass.Geometric.RelativeCohomologyExcision.Cycles

open OAI.AlgebraicGeometry.CycleClass.Thom.Open.NormalPairRestriction.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.ExteriorImageCup.Constructions.Restriction

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {M N : Type} [TopologicalSpace N]

theorem openSupportedRestriction_injective (U : Opens N) (f : M → U)
    (hc : IsClosed (Set.range (Subtype.val ∘ f))) (n : ℕ) :
    Function.Injective (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomologyMap (ModuleCat.of ℚ ℚ)
      (NormalPairRestriction.Constructions.openAmbientTransportMap Subtype.val U.isOpenEmbedding')
      (NormalPairRestriction.Constructions.openAmbientTransportMapsTo f Subtype.val U.isOpenEmbedding') n) := by
  have hKU : Set.range (Subtype.val ∘ f) ⊆ (U : Set N) := by
    rintro _ ⟨x, rfl⟩
    exact (f x).property
  have hS : (Set.range f)ᶜ = ((Geometric.LocalHomology.Cycles.subspaceInclusion (TopCat.of N) (U : Set N)) ⁻¹'
      Set.range (Subtype.val ∘ f))ᶜ := by
    congr 1
    ext z
    constructor
    · rintro ⟨x, rfl⟩
      exact ⟨x, rfl⟩
    · rintro ⟨x, hx⟩
      exact ⟨x, Subtype.ext hx⟩
  let i := Geometric.RelativeCohomologyExcision.Cycles.closedSupportCohomologyIso (TopCat.of N) (U : Set N)
    (Set.range (Subtype.val ∘ f)) hc U.isOpen hKU n
  intro a b hab
  apply i.toLinearEquiv.injective
  have h := congrArg (eqToHom (congrArg
    (fun S => AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology (ModuleCat.of ℚ ℚ) (TopCat.of U) S n) hS)) hab
  have hcast := fun c => ExteriorImageCup.Constructions.Restriction.relativeCohomologyMap_sourceCast
    (NormalPairRestriction.Constructions.openAmbientTransportMap Subtype.val U.isOpenEmbedding') hS
    (NormalPairRestriction.Constructions.openAmbientTransportMapsTo f Subtype.val U.isOpenEmbedding')
    (show Set.MapsTo (NormalPairRestriction.Constructions.openAmbientTransportMap Subtype.val U.isOpenEmbedding')
      ((Geometric.LocalHomology.Cycles.subspaceInclusion (TopCat.of N) (U : Set N)) ⁻¹' Set.range (Subtype.val ∘ f))ᶜ
      (Set.range (Subtype.val ∘ f))ᶜ from fun _ hz => hz) n c
  rw [hcast a, hcast b] at h
  exact h

end

end OAI.AlgebraicGeometry.CycleClass.Thom.Open.SupportedExcision.Constructions

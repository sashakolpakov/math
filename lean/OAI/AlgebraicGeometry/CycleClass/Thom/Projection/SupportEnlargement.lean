import OAI.AlgebraicGeometry.CycleClass.Thom.Supported.ProjectionDegree

/-! # Support Enlargement -/

namespace OAI.AlgebraicGeometry.CycleClass.Thom.Projection.SupportEnlargement.Constructions

noncomputable section

/-! Enlarging the source support inside the same bounded product preserves supported projection. -/

open _root_.CategoryTheory
open scoped _root_.Manifold

open OAI.AlgebraicGeometry.CycleClass.Thom.CompactFiberSlant.Constructions.SupportedProjection OAI.AlgebraicGeometry.CycleClass.Thom.Supported.ProjectionDegree.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.CompactFiberSlant.Constructions

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable (d : ℕ) {M : Type} [TopologicalSpace M] [T2Space M]
  [ChartedSpace (Fin d → ℂ) M] [IsManifold 𝓘(ℂ, Fin d → ℂ) 1 M]

theorem projectSupported_support (X : TopCat.{0}) (S : Set X) (K : Set M) (hK : IsCompact K)
    (T T' : Set (X × M)) (hT : T ⊆ S ×ˢ K) (hT' : T' ⊆ S ×ˢ K) (hTT : T ⊆ T') (p : ℕ)
    (c : AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology (ModuleCat.of ℚ ℚ) (TopCat.of (X × M)) Tᶜ (p + 2 * d)) :
    CompactFiberSlant.Constructions.SupportedProjection.projectSupported d X S K hK T' hT' p
      (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomologyMap (ModuleCat.of ℚ ℚ) (𝟙 (TopCat.of (X × M)))
        (A := T'ᶜ) (B := Tᶜ) (fun _ hx ht => hx (hTT ht)) (p + 2 * d) c) =
      CompactFiberSlant.Constructions.SupportedProjection.projectSupported d X S K hK T hT p c := by
  have h := ConcreteCategory.congr_hom
    (AlgebraicTopology.Cohomology.Singular.RelativeOpenSupport.relativeSingularCohomologyMap_comp (ModuleCat.of ℚ ℚ)
      (𝟙 (TopCat.of (X × M))) (𝟙 (TopCat.of (X × M)))
      (B := T'ᶜ) (C := Tᶜ)
      (CompactFiberSlant.Constructions.SupportedProjection.boundedComplementMapsTo X S K T' hT') (fun _ hx ht => hx (hTT ht)) (p + 2 * d)) c
  exact congrArg (CompactFiberSlant.Constructions.integrate d X Sᶜ K hK p) h

theorem projectAt_support (X : TopCat.{0}) (S : Set X) (K : Set M) (hK : IsCompact K)
    (T T' : Set (X × M)) (hT : T ⊆ S ×ˢ K) (hT' : T' ⊆ S ×ˢ K) (hTT : T ⊆ T')
    (p n : ℕ) (hn : p + 2 * d = n)
    (c : AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology (ModuleCat.of ℚ ℚ) (TopCat.of (X × M)) Tᶜ n) :
    Supported.ProjectionDegree.Constructions.projectAt d X S K hK T' hT' p n hn
      (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomologyMap (ModuleCat.of ℚ ℚ) (𝟙 (TopCat.of (X × M)))
        (A := T'ᶜ) (B := Tᶜ) (fun _ hx ht => hx (hTT ht)) n c) =
      Supported.ProjectionDegree.Constructions.projectAt d X S K hK T hT p n hn c := by
  subst n
  exact projectSupported_support d X S K hK T T' hT hT' hTT p c

end

end OAI.AlgebraicGeometry.CycleClass.Thom.Projection.SupportEnlargement.Constructions

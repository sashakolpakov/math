import OAI.AlgebraicGeometry.CycleClass.Thom.Projection.SupportEnlargement
import OAI.AlgebraicGeometry.CycleClass.Thom.ImageIntersectionTo

/-! # Projected Image Support Change -/

namespace OAI.AlgebraicGeometry.CycleClass.Thom.ProjectedImageSupportChange.Constructions

noncomputable section

/-! Replacing an image parametrization by another with exactly the same
image preserves the projected supported intersection class. -/

open _root_.CategoryTheory
open scoped _root_.Manifold

open OAI.AlgebraicGeometry.CycleClass.Thom.Supported.ProjectionDegree.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.Projection.SupportEnlargement.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.ImageIntersectionCup.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.ImageIntersectionTo.Constructions.Restriction

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable (d : ℕ) {M : Type} [TopologicalSpace M] [T2Space M]
  [ChartedSpace (Fin d → ℂ) M] [IsManifold 𝓘(ℂ, Fin d → ℂ) 1 M]

theorem projectAt_secondImage_change (X : TopCat.{0}) {L P Q : Type}
    (u : L → X × M) (v : P → X × M) (w : Q → X × M) (hvw : Set.range v = Set.range w)
    (hu : IsOpen (Set.range u)ᶜ) (hv : IsOpen (Set.range v)ᶜ) (hw : IsOpen (Set.range w)ᶜ)
    (S : Set X) (K : Set M) (hK : IsCompact K)
    (hT : Set.range u ∩ Set.range v ⊆ S ×ˢ K) (hT' : Set.range u ∩ Set.range w ⊆ S ×ˢ K)
    (p q r : ℕ) (hn : r + 2 * d = 2 * (p + q))
    (a : AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology (ModuleCat.of ℚ ℚ) (TopCat.of (X × M)) (Set.range u)ᶜ (2 * p))
    (b : AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology (ModuleCat.of ℚ ℚ) (TopCat.of (X × M)) (Set.range v)ᶜ (2 * q)) :
    Supported.ProjectionDegree.Constructions.projectAt d X S K hK (Set.range u ∩ Set.range v) hT r (2 * (p + q)) hn
      (ImageIntersectionCup.Constructions.imageIntersectionCup u v hu hv p q a b) =
    Supported.ProjectionDegree.Constructions.projectAt d X S K hK (Set.range u ∩ Set.range w) hT' r (2 * (p + q)) hn
      (ImageIntersectionCup.Constructions.imageIntersectionCup u w hu hw p q a
        (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomologyMap (ModuleCat.of ℚ ℚ) (𝟙 (TopCat.of (X × M)))
          (A := (Set.range w)ᶜ) (B := (Set.range v)ᶜ)
          (fun x hx hy => hx ((Set.ext_iff.mp hvw x).mp hy)) (2 * q) b)) := by
  have hs : Set.MapsTo (𝟙 (TopCat.of (X × M))) (Set.range w)ᶜ (Set.range v)ᶜ :=
    fun x hx hy => hx ((Set.ext_iff.mp hvw x).mp hy)
  have he := ImageIntersectionTo.Constructions.Restriction.imageIntersectionCup_restriction u v u w (𝟙 (TopCat.of (X × M)))
    (fun _ hx => hx) hs hu hv hu hw p q a b
  simp only [AlgebraicTopology.Cohomology.Singular.RelativeOpenSupport.relativeSingularCohomologyMap_id, CategoryTheory.id_apply] at he
  have hp := Projection.SupportEnlargement.Constructions.projectAt_support d X S K hK (Set.range u ∩ Set.range v) (Set.range u ∩ Set.range w)
    hT hT' (fun x hx => ⟨hx.1, (Set.ext_iff.mp hvw x).mp hx.2⟩) r (2 * (p + q)) hn
    (ImageIntersectionCup.Constructions.imageIntersectionCup u v hu hv p q a b)
  exact hp.symm.trans (congrArg
    (Supported.ProjectionDegree.Constructions.projectAt d X S K hK (Set.range u ∩ Set.range w) hT' r (2 * (p + q)) hn) he)

end

end OAI.AlgebraicGeometry.CycleClass.Thom.ProjectedImageSupportChange.Constructions

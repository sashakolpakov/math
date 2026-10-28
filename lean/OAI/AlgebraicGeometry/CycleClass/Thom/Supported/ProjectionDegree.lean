import OAI.AlgebraicGeometry.CycleClass.Thom.CompactFiberSlant

/-! # Projection Degree -/

namespace OAI.AlgebraicGeometry.CycleClass.Thom.Supported.ProjectionDegree.Constructions

noncomputable section

/-! Supported projection with its input degree specified by an actual equality. -/

open _root_.CategoryTheory
open scoped _root_.Manifold

open OAI.AlgebraicGeometry.CycleClass.Thom.CompactFiberSlant.Constructions.SupportedProjection

variable (d : ℕ) {M : Type} [TopologicalSpace M] [T2Space M]
  [ChartedSpace (Fin d → ℂ) M] [IsManifold 𝓘(ℂ, Fin d → ℂ) 1 M]

def projectAt (X : TopCat.{0}) (S : Set X) (K : Set M) (hK : IsCompact K)
    (T : Set (X × M)) (hT : T ⊆ S ×ˢ K) (p n : ℕ) (hn : p + 2 * d = n) :
    AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology (ModuleCat.of ℚ ℚ) (TopCat.of (X × M)) Tᶜ n →ₗ[ℚ]
      AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology (ModuleCat.of ℚ ℚ) X Sᶜ p :=
  (CompactFiberSlant.Constructions.SupportedProjection.projectSupported d X S K hK T hT p).comp
    (eqToHom (congrArg (fun j => AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology (ModuleCat.of ℚ ℚ)
      (TopCat.of (X × M)) Tᶜ j) hn.symm)).hom

theorem projectAt_cast (X : TopCat.{0}) (S : Set X) (K : Set M) (hK : IsCompact K)
    (T : Set (X × M)) (hT : T ⊆ S ×ˢ K) (p n : ℕ) (hn : p + 2 * d = n)
    (c : AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology (ModuleCat.of ℚ ℚ) (TopCat.of (X × M)) Tᶜ (p + 2 * d)) :
    projectAt d X S K hK T hT p n hn
      (eqToHom (congrArg (fun j => AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology (ModuleCat.of ℚ ℚ)
        (TopCat.of (X × M)) Tᶜ j) hn) c) = CompactFiberSlant.Constructions.SupportedProjection.projectSupported d X S K hK T hT p c := by
  subst n
  rfl

end

end OAI.AlgebraicGeometry.CycleClass.Thom.Supported.ProjectionDegree.Constructions

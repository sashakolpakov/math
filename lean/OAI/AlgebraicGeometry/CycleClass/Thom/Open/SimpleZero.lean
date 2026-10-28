import OAI.AlgebraicGeometry.CycleClass.Thom.Open.InclusionLocalInverse
import OAI.AlgebraicGeometry.CycleClass.Thom.LocalDualLocalInverse

/-! # Simple Zero -/

namespace OAI.AlgebraicGeometry.CycleClass.Thom.Open.SimpleZero.Constructions.Class

noncomputable section

/-! The local normal class of a simple zero on an actual open set is the inherited canonical point class. -/

open _root_.CategoryTheory _root_.TopologicalSpace
open scoped _root_.Manifold ContDiff

open OAI.AlgebraicGeometry.CycleClass.Thom.Open.InclusionLocalInverse.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.CanonicalLocalDual.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.CanonicalLocalDualCoordinates.Constructions
open OAI.AlgebraicGeometry.CycleClass.Thom.LocalDualLocalInverse.Constructions.Canonical

theorem simpleZero_class (d : ℕ) {M : Type} [TopologicalSpace M] [T2Space M]
    [ChartedSpace (Fin d → ℂ) M] [IsManifold 𝓘(ℂ, Fin d → ℂ) ω M]
    (q : M → (Fin d → ℂ)) (U : Opens M) (x : U)
    (hq : IsLocalDiffeomorphAt 𝓘(ℂ, Fin d → ℂ) 𝓘(ℂ, Fin d → ℂ) ω q x.val)
    (g : TopCat.of U ⟶ TopCat.of (Fin d → ℂ)) (hg : (g : U → (Fin d → ℂ)) = q ∘ Subtype.val)
    (hx : g x = 0) (hp : Set.MapsTo g ({x}ᶜ) ({0}ᶜ)) :
    AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomologyMap (ModuleCat.of ℚ ℚ) g hp (2 * d)
      (Geometric.RationalLocalPurity.Cycles.complexNormalRationalDualClass d) = CanonicalLocalDual.Constructions.canonicalLocalDual d x := by
  have h := IsLocalDiffeomorphAt.comp (K := 𝓘(ℂ, Fin d → ℂ)) (P := Fin d → ℂ)
    (InclusionLocalInverse.Constructions.inclusion_localInverse U x) hq
  rw [← hg] at h
  obtain ⟨e, he, hge⟩ := h
  rw [← CanonicalLocalDualCoordinates.Constructions.canonicalLocalDual_zero]
  exact LocalDualLocalInverse.Constructions.Canonical.canonicalLocalDual_pullback_localInverse d g x 0 hx hp e he hge

end

end OAI.AlgebraicGeometry.CycleClass.Thom.Open.SimpleZero.Constructions.Class

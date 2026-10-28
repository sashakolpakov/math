import OAI.AlgebraicGeometry.DivisorClass.Chern.OpenNaturality
import OAI.AlgebraicGeometry.DivisorClass.Chern.Component

/-! # Components -/

namespace OAI.AlgebraicGeometry.DivisorClass.Chern

noncomputable section

/-!
# ChernClass: actual first Chern classes on all integral components

Each coordinate of the native singular-cohomology decomposition is the
original first Chern class of the actual restricted module sheaf. This
also gives an exact componentwise criterion for the requested geometric
divisor comparison, including empty and disconnected presentations.
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

variable {X : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation} (L : Line.Bundles.AlgebraicLineBundle X)

/-- Actual component restriction of the independently constructed logarithmic Chern class. -/
theorem Line.Bundles.AlgebraicLineBundle.firstChernClassQ_components (C : irreducibleComponents X.carrier) :
    X.componentBettiEquiv (ModuleCat.of ℚ ℚ) 2 (First.firstChernClassQ X L) C =
      First.firstChernClassQ (X.componentVariety C).presentation (L.componentLineBundle C) := by
  rw [X.componentBettiEquiv_apply]
  exact (OpenNaturality.firstChernClassQ_restrictToOpen L (X.componentInclusionOver C)).symm

/-- The geometric divisor comparison on the original presentation is
equivalent to the same actual comparison on every genuine component. -/
theorem Line.Bundles.AlgebraicLineBundle.firstChernClassQ_eq_algebraicDivisorClass_iff_components :
    First.firstChernClassQ X L = L.algebraicDivisorClass ↔
      ∀ C : irreducibleComponents X.carrier,
        First.firstChernClassQ (X.componentVariety C).presentation (L.componentLineBundle C) =
          (X.componentVariety C).geometricCycleClassMap 1 (L.componentRationalDivisor C) := by
  constructor
  · intro h C
    rw [← L.firstChernClassQ_components C, h, L.algebraicDivisorClass_components]
  · intro h
    apply (X.componentBettiEquiv (ModuleCat.of ℚ ℚ) 2).injective
    funext C
    rw [L.firstChernClassQ_components, L.algebraicDivisorClass_components]
    exact h C

end

end OAI.AlgebraicGeometry.DivisorClass.Chern

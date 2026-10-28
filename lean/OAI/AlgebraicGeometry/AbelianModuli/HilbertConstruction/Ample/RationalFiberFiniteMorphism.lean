import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Ample.RationalFiberFiniteness
import Mathlib.AlgebraicGeometry.Morphisms.QuasiFinite

/-! # Rational Fiber Finite Morphism -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Ample.RationalFiberFiniteMorphism

noncomputable section

/-! Proper rational fibers with finite support are finite schemes over the field. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

variable {K : Type u} [Field K] [IsAlgClosed K] {Y Z : Scheme.{u}}

theorem ample_pullback_rationalFiber_isFinite (f : Y ⟶ Z) [IsProper f]
    (a : Spec (.of K) ⟶ Z) [IsClosedImmersion a] (L : Line.Bundles.LineBundle Z)
    (hL : (L.pullback f).IsAmple) : IsFinite (Limits.pullback.snd f a) := by
  have : Finite (Limits.pullback f a : Scheme.{u}) := RationalFiberFiniteness.ample_pullback_rationalFiber_finite f a L hL
  have : LocallyQuasiFinite (Limits.pullback.snd f a) :=
    LocallyQuasiFinite.of_finite_preimage_singleton _ (fun _ => Set.toFinite _)
  exact IsFinite.of_locallyQuasiFinite (Limits.pullback.snd f a)

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Ample.RationalFiberFiniteMorphism

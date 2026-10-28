import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.ContractedAmpleFiniteness

/-! # Rational Fiber Finiteness -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Ample.RationalFiberFiniteness

noncomputable section

/-! Rational fibers of a proper map with ample pullback have finitely many points. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

variable {K : Type u} [Field K] [IsAlgClosed K] {Y Z : Scheme.{u}}

theorem ample_pullback_rationalFiber_finite (f : Y ⟶ Z) [IsProper f]
    (a : Spec (.of K) ⟶ Z) [IsClosedImmersion a] (L : Line.Bundles.LineBundle Z)
    (hL : (L.pullback f).IsAmple) : Finite (Limits.pullback f a : Scheme.{u}) := by
  let p : Limits.pullback f a ⟶ Spec (.of K) := Limits.pullback.snd f a
  have : IsProper p := inferInstanceAs (IsProper (Limits.pullback.snd f a))
  have : CompactSpace (Limits.pullback f a : Scheme.{u}) := (quasiCompact_iff_compactSpace p).mp inferInstance
  have : IsNoetherian (Limits.pullback f a) := { __ := LocallyOfFiniteType.isLocallyNoetherian p }
  exact ContractedAmpleFiniteness.contracted_ample_noetherian_finite p f (Limits.pullback.fst f a) a Limits.pullback.condition L hL

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Ample.RationalFiberFiniteness

import OAI.AlgebraicGeometry.FormalGeometry.Completion.NormalizedProductCoverFunctions
import OAI.AlgebraicGeometry.FormalGeometry.Completion.RationalFiberConnected

/-! # Etale Product Cover Connected -/

namespace OAI.AlgebraicGeometry.FormalGeometry.Completion.Finite.EtaleProductCoverConnected.Construction

noncomputable section

/-! Connected fibers for the sectioned component of a finite etale product cover. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

universe u

variable {K : Type u} [Field K] [IsAlgClosed K] {A B T : Scheme.{u}}
  [IsIntegral A] [IsIntegral B]
  (p : A ⟶ Spec (CommRingCat.of K)) [IsProper p] [Smooth p]
  (q : B ⟶ Spec (CommRingCat.of K)) [IsProper q] [Smooth q]
  (t : T ⟶ pullback p q) [IsFinite t] [Etale t]
  [IsIso (t ≫ pullback.snd p q).fromNormalization]

/-- Once its actual normalization base is B, the product cover has connected actual fibers. -/
theorem finiteEtaleProductCover_fiber_connected (b : B) :
    ConnectedSpace ((t ≫ pullback.snd p q).fiber b) :=
  NormalizationFiberConnected.Construction.fiber_connected_of_normalization (t ≫ pullback.snd p q)
    (NormalizedProductCoverFunctions.Construction.finiteEtaleProductCover_normalized_fiber_connected p q t) b

/-- The actual base change along a rational point of B is connected. -/
theorem finiteEtaleProductCover_rational_fiber_connected
    (b : Spec (CommRingCat.of K) ⟶ B) (hb : b ≫ q = 𝟙 _) :
    ConnectedSpace (pullback (t ≫ pullback.snd p q) b : Scheme.{u}) := by
  have := finiteEtaleProductCover_fiber_connected p q t (b (IsLocalRing.closedPoint K))
  exact RationalFiberConnected.Construction.rationalPoint_pullback_connected (t ≫ pullback.snd p q) q b hb

end

end OAI.AlgebraicGeometry.FormalGeometry.Completion.Finite.EtaleProductCoverConnected.Construction

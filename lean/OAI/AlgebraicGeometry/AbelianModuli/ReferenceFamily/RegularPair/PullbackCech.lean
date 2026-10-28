import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.RegularPair.PairPullback

/-! # Pullback Cech -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.RegularPair.PullbackCech

noncomputable section

/-! Pullback of the literal Čech cocycle of regular pair sections is
the Čech cocycle of their original scheme-theoretic pullbacks. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace

variable {X Y : Scheme.{0}} (f : X ⟶ Y) {I : Type} (U : I → Y.Opens)
    (v : ∀ i j : I, Γ(Y, U i ⊓ U j))

theorem regularPairPullback_cech :
    StructureCechPullbackData.structureCechPullback f U 1 (Closed.regularPairCechCochain Y U v) =
      Closed.regularPairCechCochain X (fun i => f ⁻¹ᵁ U i) (PairPullback.regularPairPullback f U v) := by
  funext t
  have h : AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection U t ≤ U (t 0) ⊓ U (t 1) :=
    le_inf (AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection_le U t 0) (AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection_le U t 1)
  have hn := PairPullback.regularSectionPullback_restrict f h (v (t 0) (t 1))
  change X.presheaf.map _ (f.app _ (Y.presheaf.map (homOfLE h).op (v (t 0) (t 1)))) =
    X.presheaf.map _ (f.app _ (v (t 0) (t 1)))
  rw [hn, ← CommRingCat.comp_apply, ← Functor.map_comp]
  congr 1

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.RegularPair.PullbackCech

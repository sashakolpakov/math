import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Pure.Fine

/-! # Hilbert Construction Interface -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.HilbertConstructionInterface

noncomputable section

/-! Implementation of the proposed interfaces in the committed HilbertConstruction statement.
The full statement retains every dimension, polarization type, level, base,
test scheme, and polarized family. Its equivalence with the bundled pure
input is proved here; neither formulation assumes a PEL parameter space.
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry

/-- Finite type and an actual open immersion followed by an actual
projective morphism, presented by a closed immersion into projective space.
This implements the proposed `IsQuasiProjective` interface of HilbertConstruction. -/
def QuasiProjective {X S : Scheme.{0}} (f : X ⟶ S) : Prop :=
  LocallyOfFiniteType f ∧ QuasiCompact f ∧
    ∃ (Y : Scheme.{0}) (p : Y ⟶ S) (j : X ⟶ Y),
      IsOpenImmersion j ∧ j ≫ p = f ∧
        ∃ (n : ℕ) (i : Over.mk p ⟶ HilbertConstruction.Projective.ProjectivePresentations.projectiveSpaceOver S n),
          IsClosedImmersion i.left

theorem e33QuasiProjective_iff_presentation {S : Scheme.{0}} (X : Over S) :
    QuasiProjective X.hom ↔ Nonempty (HilbertConstruction.Projective.ProjectivePresentations.QuasiProjectivePresentation X) := by
  constructor
  · rintro ⟨hft, hqc, Y, p, j, hj, hcomp, n, i, hi⟩
    exact ⟨{
      locallyFiniteType := hft
      quasiCompact := hqc
      compactification := Over.mk p
      projective := { dimension := n, embedding := i, closedImmersion := hi }
      embedding := Over.homMk j hcomp
      openImmersion := hj }⟩
  · rintro ⟨P⟩
    exact ⟨P.locallyFiniteType, P.quasiCompact, P.compactification.left,
      P.compactification.hom, P.embedding.left, P.openImmersion, P.embedding.w,
      P.projective.dimension, P.projective.embedding, P.projective.closedImmersion⟩

/-- The complete quantifier scope and conclusion of committed HilbertConstruction, with
its proposed polarized-family, pullback, and isomorphism interfaces supplied
by their native implementations. This is an explicit prerequisite type. -/
def HilbertConstructionFullStatement : Prop :=
  ∀ (g : ℕ), 0 < g →
    ∀ (δ : Fin g → ℕ), (∀ i, 0 < δ i) →
      (∀ i j, i ≤ j → δ i ∣ δ j) →
    ∀ (N : ℕ), 3 ≤ N → Nat.Coprime N (∏ i, δ i) →
    ∀ (S : Scheme.{0}), IsUnit (N : Γ(S, ⊤)) →
      (∀ i, IsUnit (δ i : Γ(S, ⊤))) →
    ∃ (M : Over S) (U : HilbertConstruction.PolarizationData.PolarizedAbelianWithFullLevel g δ N M.left),
      QuasiProjective M.hom ∧
      ∀ (T : Over S) (A : HilbertConstruction.PolarizationData.PolarizedAbelianWithFullLevel g δ N T.left),
        ∃! f : T ⟶ M,
          Nonempty (HilbertConstruction.Moduli.Isomorphisms.LevelPreservingIso (U.pullback f.left) A)

theorem e33FullStatement_iff_pureHilbertConstructionInput : HilbertConstructionFullStatement ↔ Pure.Fine.PureHilbertConstructionInput := by
  constructor
  · intro h g hg δ hδ hchain N hN hcoprime S hunit hδunit
    obtain ⟨M, U, hM, hfine⟩ := h g hg δ hδ hchain N hN hcoprime S hunit hδunit
    exact ⟨⟨M, U⟩, (e33QuasiProjective_iff_presentation M).mp hM, hfine⟩
  · intro h g hg δ hδ hchain N hN hcoprime S hunit hδunit
    obtain ⟨M, hM, hfine⟩ := h g hg δ hδ hchain N hN hcoprime S hunit hδunit
    exact ⟨M.space, M.universal,
      (e33QuasiProjective_iff_presentation M.space).mpr hM, hfine⟩

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.HilbertConstructionInterface

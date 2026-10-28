import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Moduli.BaseChange
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Projective.ProjectivePresentations
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Level.Data

/-! # Fine -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Pure.Fine

noncomputable section

/-! The selected HilbertConstruction input, stated on the implemented pure polarized
moduli objects and actual quasi-projective presentations. It concerns
only the pure problem at a tame auxiliary level; no PEL model,
PEL representability, or analytic comparison is assumed. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

structure PurePolarizedModel (g : ℕ) (δ : Fin g → ℕ) (L : ℕ) (S : Scheme.{0}) where
  space : Over S
  universal : HilbertConstruction.PolarizationData.PolarizedAbelianWithFullLevel g δ L space.left

def PurePolarizedModel.IsFine {g L : ℕ} {δ : Fin g → ℕ} {S : Scheme.{0}}
    (M : PurePolarizedModel g δ L S) : Prop :=
  ∀ (T : Over S) (A : HilbertConstruction.PolarizationData.PolarizedAbelianWithFullLevel g δ L T.left),
    ∃! f : T ⟶ M.space, Nonempty (HilbertConstruction.Moduli.Isomorphisms.LevelPreservingIso (M.universal.pullback f.left) A)

/-- Exact pure HilbertConstruction graph input, with its proposed interfaces implemented.
This is an explicit theorem parameter, never an axiom declaration. -/
def PureHilbertConstructionInput : Prop :=
  ∀ (g : ℕ), 0 < g → ∀ (δ : Fin g → ℕ), (∀ i, 0 < δ i) →
    (∀ i j, i ≤ j → δ i ∣ δ j) →
    ∀ (L : ℕ), 3 ≤ L → Nat.Coprime L (∏ i, δ i) →
    ∀ (S : Scheme.{0}), IsUnit (L : Γ(S, ⊤)) → (∀ i, IsUnit (δ i : Γ(S, ⊤))) →
      ∃ M : PurePolarizedModel g δ L S,
        Nonempty (HilbertConstruction.Projective.ProjectivePresentations.QuasiProjectivePresentation M.space) ∧ M.IsFine

theorem positive_integer_unit_on_field_base {K : Type} [Field K] [CharZero K]
    {S : Scheme.{0}} (p : S ⟶ Spec (.of K)) (n : ℕ) (hn : 0 < n) : IsUnit (n : Γ(S, ⊤)) := by
  let constants : K →+* Γ(S, ⊤) := p.appTop.hom.comp (Scheme.ΓSpecIso (.of K)).inv.hom
  have h : IsUnit (n : K) := isUnit_iff_ne_zero.mpr (Nat.cast_ne_zero.mpr (Nat.ne_of_gt hn))
  simpa only [map_natCast] using h.map constants

theorem exists_auxiliary_pure_moduli (h33 : PureHilbertConstructionInput)
    {K : Type} [Field K] [CharZero K] (g : ℕ) (hg : 0 < g) (δ : Fin g → ℕ)
    (hδ : ∀ i, 0 < δ i) (hchain : ∀ i j, i ≤ j → δ i ∣ δ j)
    (N : ℕ) (hN : 0 < N) :
    ∃ L : ℕ, 3 ≤ L ∧ Nat.Coprime L (∏ i, δ i) ∧ Nat.Coprime L N ∧
      ∃ M : PurePolarizedModel g δ L (Spec (.of K)),
        Nonempty (HilbertConstruction.Projective.ProjectivePresentations.QuasiProjectivePresentation M.space) ∧ M.IsFine := by
  have hD : 0 < ∏ i, δ i := Finset.prod_pos (fun i _ => hδ i)
  obtain ⟨L, hL, hLD, hLN⟩ := Level.Data.exists_auxiliary_level (∏ i, δ i) N hD hN
  obtain ⟨M, hM, hf⟩ := h33 g hg δ hδ hchain L hL hLD (Spec (.of K))
    (positive_integer_unit_on_field_base (𝟙 (Spec (.of K))) L (by omega))
    (fun i => positive_integer_unit_on_field_base (𝟙 (Spec (.of K))) (δ i) (hδ i))
  exact ⟨L, hL, hLD, hLN, M, hM, hf⟩

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Pure.Fine

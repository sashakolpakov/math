import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Finite.FieldPointRankCriterion
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Isogeny.KernelScheme

/-! # Kernel Geometric Etale -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction

noncomputable section

/-! The specified positive polarization type identifies every geometric kernel's point count with its finite-flat degree, so the actual geometric kernel scheme is etale. -/
open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj BigOperators
universe u

theorem Abelian.Schemes.AbelianScheme.Isogeny.HasPolarizationType.kernel_points_card
    {K : Type u} [Field K] [IsAlgClosed K] {g : ℕ}
    {A B : Abelian.Schemes.AbelianScheme g (Spec (.of K))} {p : Abelian.Schemes.AbelianScheme.Isogeny A B} {δ : Fin g → ℕ}
    (hp : p.HasPolarizationType δ) (hδ : ∀ i, 0 < δ i) :
    Nat.card (Over.mk (𝟙 (Spec (.of K))) ⟶ p.kernelScheme) = (∏ i, δ i) ^ 2 := by
  classical
  have hδnz (i : Fin g) : NeZero (δ i) := ⟨Nat.ne_of_gt (hδ i)⟩
  obtain ⟨e⟩ := hp.geometricKernel K (𝟙 _)
  calc
    _ = Nat.card (p.kernelAt (Over.mk (𝟙 (Spec (.of K))))) :=
      Nat.card_congr (p.kernelSchemePointsEquiv _)
    _ = Nat.card (Multiplicative ((∀ i : Fin g, ZMod (δ i)) × (∀ i : Fin g, ZMod (δ i)))) :=
      Nat.card_congr e.toEquiv
    _ = _ := by simp [Nat.card_eq_fintype_card, Fintype.card_pi, sq]

theorem Abelian.Schemes.AbelianScheme.Isogeny.HasPolarizationType.kernel_etale_overAlgClosed
    {K : Type u} [Field K] [IsAlgClosed K] {g : ℕ}
    {A B : Abelian.Schemes.AbelianScheme g (Spec (.of K))} {p : Abelian.Schemes.AbelianScheme.Isogeny A B} {δ : Fin g → ℕ}
    (hp : p.HasPolarizationType δ) (hδ : ∀ i, 0 < δ i) : Etale p.kernelScheme.hom := by
  let x := IsLocalRing.closedPoint K
  apply Finite.FieldPointRankCriterion.finiteFieldScheme_etale_of_point_card_eq p.kernelScheme x
  exact (hp.kernel_points_card hδ).trans
    ((p.kernelScheme_finrank x).trans (hp.degree (η[B.scheme].left x))).symm

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction

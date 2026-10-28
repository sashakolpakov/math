import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Polarization.KernelGeometricEtale

/-! # Kernel Geometric Points -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction

noncomputable section

/-! Geometric base changes of the actual isogeny kernel have precisely the specified geometric kernel points and the specified finite rank. -/
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj BigOperators
universe u

variable {S : Scheme.{u}} {g h : ℕ} {A : Abelian.Schemes.AbelianScheme g S} {B : Abelian.Schemes.AbelianScheme h S}

def Abelian.Schemes.AbelianScheme.Isogeny.kernelGeometricPointsEquiv (p : Abelian.Schemes.AbelianScheme.Isogeny A B)
    {K : Type u} [Field K] (s : Spec (.of K) ⟶ S) :
    (Over.mk (𝟙 (Spec (.of K))) ⟶ (Over.pullback s).obj p.kernelScheme) ≃ p.kernelAt (Over.mk s) := by
  let e : (Over.map s).obj (Over.mk (𝟙 (Spec (.of K)))) ≅ Over.mk s :=
    Over.isoMk (Iso.refl _) (by simp)
  exact ((Over.mapPullbackAdj s).homEquiv (Over.mk (𝟙 (Spec (.of K)))) p.kernelScheme).symm.trans
    ((e.homCongr (Iso.refl p.kernelScheme)).trans (p.kernelSchemePointsEquiv (Over.mk s)))

theorem Abelian.Schemes.AbelianScheme.Isogeny.HasPolarizationType.kernel_geometricBaseChange_points_card
    {A B : Abelian.Schemes.AbelianScheme g S} {p : Abelian.Schemes.AbelianScheme.Isogeny A B} {δ : Fin g → ℕ}
    (hp : p.HasPolarizationType δ) (hδ : ∀ i, 0 < δ i)
    (K : Type u) [Field K] [IsAlgClosed K] (s : Spec (.of K) ⟶ S) :
    Nat.card (Over.mk (𝟙 (Spec (.of K))) ⟶ (Over.pullback s).obj p.kernelScheme) = (∏ i, δ i) ^ 2 := by
  classical
  have hδnz (i : Fin g) : NeZero (δ i) := ⟨Nat.ne_of_gt (hδ i)⟩
  obtain ⟨e⟩ := hp.geometricKernel K s
  calc
    _ = Nat.card (p.kernelAt (Over.mk s)) := Nat.card_congr (p.kernelGeometricPointsEquiv s)
    _ = Nat.card (Multiplicative ((∀ i : Fin g, ZMod (δ i)) × (∀ i : Fin g, ZMod (δ i)))) :=
      Nat.card_congr e.toEquiv
    _ = _ := by simp [Nat.card_eq_fintype_card, Fintype.card_pi, sq]

theorem Abelian.Schemes.AbelianScheme.Isogeny.HasPolarizationType.kernel_geometricBaseChange_etale
    {A B : Abelian.Schemes.AbelianScheme g S} {p : Abelian.Schemes.AbelianScheme.Isogeny A B} {δ : Fin g → ℕ}
    (hp : p.HasPolarizationType δ) (hδ : ∀ i, 0 < δ i)
    (K : Type u) [Field K] [IsAlgClosed K] (s : Spec (.of K) ⟶ S) :
    Etale (pullback.snd p.kernelScheme.hom s) := by
  let M := (Over.pullback s).obj p.kernelScheme
  have : IsFinite M.hom := inferInstanceAs (IsFinite (pullback.snd p.kernelScheme.hom s))
  let x := IsLocalRing.closedPoint K
  apply Finite.FieldPointRankCriterion.finiteFieldScheme_etale_of_point_card_eq M x
  exact (hp.kernel_geometricBaseChange_points_card hδ K s).trans
    (((Scheme.Hom.finrank_pullback_snd p.kernelScheme.hom s x).trans
      (p.kernelScheme_finrank (s x))).trans (hp.degree (η[B.scheme].left (s x)))).symm

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction

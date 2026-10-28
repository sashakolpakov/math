import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Pure.PullbackRigidity
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Embedded.IsomorphismUniqueness

/-! # Pullback Iso Uniqueness -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Pure.PullbackIsoUniqueness

noncomputable section

/-! Every full-level polarized comparison from an arbitrary pullback of
a finite-type pure family is unique. This includes its actual dual and
Poincare data, and supplies coherence for chosen descent comparisons. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

theorem pure_abelian_eq_id
    {K : Type} [Field K] [CharZero K] [Countable K]
    {X : Scheme.{0}} (p : X ⟶ Spec (.of K)) [LocallyOfFiniteType p]
    {g N : ℕ} {δ : Fin g → ℕ}
    (A : HilbertConstruction.PolarizationData.PolarizedAbelianWithFullLevel g δ N X) (hN : 3 ≤ N)
    (e : HilbertConstruction.Moduli.Isomorphisms.LevelPreservingIso A A) : e.abelian.hom = 𝟙 A.abelian.scheme :=
  AutomorphismDescent.pure_abelian_eq_id_via e (HilbertConstruction.Moduli.Isomorphisms.LevelPreservingIso.pullbackId A).symm
    (fun d => PullbackRigidity.purePullback_abelian_eq_id p A hN (𝟙 X) d)

theorem pure_levelIso_subsingleton
    {K : Type} [Field K] [CharZero K] [Countable K]
    {X : Scheme.{0}} (p : X ⟶ Spec (.of K)) [LocallyOfFiniteType p]
    {g N : ℕ} {δ : Fin g → ℕ}
    (A : HilbertConstruction.PolarizationData.PolarizedAbelianWithFullLevel g δ N X) (hN : 3 ≤ N)
    (B : HilbertConstruction.PolarizationData.PolarizedAbelianWithFullLevel g δ N X) :
    Subsingleton (HilbertConstruction.Moduli.Isomorphisms.LevelPreservingIso A B) := by
  constructor
  intro a b
  apply HilbertConstruction.Moduli.Isomorphisms.LevelPreservingIso.ext_abelian
  have h := pure_abelian_eq_id p A hN (a.trans b.symm)
  change a.abelian.hom ≫ b.abelian.inv = 𝟙 A.abelian.scheme at h
  apply (cancel_mono b.abelian.inv).mp
  exact h.trans b.abelian.hom_inv_id.symm

theorem purePullback_levelIso_subsingleton
    {K : Type} [Field K] [CharZero K] [Countable K]
    {X S : Scheme.{0}} (p : X ⟶ Spec (.of K)) [LocallyOfFiniteType p]
    {g N : ℕ} {δ : Fin g → ℕ}
    (A : HilbertConstruction.PolarizationData.PolarizedAbelianWithFullLevel g δ N X)
    (hN : 3 ≤ N) (t : S ⟶ X) (B : HilbertConstruction.PolarizationData.PolarizedAbelianWithFullLevel g δ N S) :
    Subsingleton (HilbertConstruction.Moduli.Isomorphisms.LevelPreservingIso (A.pullback t) B) := by
  constructor
  intro a b
  apply HilbertConstruction.Moduli.Isomorphisms.LevelPreservingIso.ext_abelian
  have h := PullbackRigidity.purePullback_abelian_eq_id p A hN t (a.trans b.symm)
  change a.abelian.hom ≫ b.abelian.inv = 𝟙 (A.abelian.pullback t).scheme at h
  apply (cancel_mono b.abelian.inv).mp
  exact h.trans b.abelian.hom_inv_id.symm

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Pure.PullbackIsoUniqueness

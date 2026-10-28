import OAI.AlgebraicGeometry.GroupSchemes.EtalePointFunctor
import OAI.AlgebraicGeometry.GroupSchemes.EtaleGenerators

/-! # Etale Classification -/

namespace OAI.AlgebraicGeometry.GroupSchemes

noncomputable section

/-! Classification of the split étale branch as an actual all-affine tower isomorphism. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry Opposite WithConv _root_.CategoryTheory.MonObj

universe u
variable {k : Type u} [Field k] [IsAlgClosed k]
variable {p : ℕ} [Fact p.Prime]

/-- Compatible cyclic coordinates on locally constant point functions. -/
def FiniteEtale.PDivisibleGroup.cyclicLocallyConstantEquiv (G : FiniteEtale.PDivisibleGroup k p 1)
    (hsplit : ∀ n, Algebra.IsFiniteSplit k (G.level n).algebra)
    (n : ℕ) (R : CommAlgCat.{u} k) :
    LocallyConstant (PrimeSpectrum R) (G.level n).rationalPoints ≃*
      LocallyConstant (PrimeSpectrum R) (Multiplicative (ZMod (p ^ n))) where
  toEquiv := LocallyConstant.congrRight (G.cyclicPointEquiv hsplit n).symm.toEquiv
  map_mul' x y := by
    apply LocallyConstant.ext
    intro P
    exact (G.cyclicPointEquiv hsplit n).symm.map_mul (x P) (y P)

/-- The standard cyclic group identification on every affine algebra. -/
def FiniteEtale.PDivisibleGroup.etaleLevelPointEquiv (G : FiniteEtale.PDivisibleGroup k p 1)
    (hsplit : ∀ n, Algebra.IsFiniteSplit k (G.level n).algebra)
    (n : ℕ) (R : CommAlgCat.{u} k) :
    (G.level n).points.obj R ≃* (FiniteEtale.etaleLevel k p n).obj R := by
  have := hsplit n
  exact ((G.level n).etalePointsMulEquiv R).trans (G.cyclicLocallyConstantEquiv hsplit n R)

/-- Naturality on all affine algebras of the standard cyclic identification. -/
def FiniteEtale.PDivisibleGroup.etaleLevelPointIso (G : FiniteEtale.PDivisibleGroup k p 1)
    (hsplit : ∀ n, Algebra.IsFiniteSplit k (G.level n).algebra) (n : ℕ) :
    (G.level n).points ≅ FiniteEtale.etaleLevel k p n :=
  NatIso.ofComponents (fun R => (G.etaleLevelPointEquiv hsplit n R).toCommGrpIso) (by
    intro R S a
    apply CommGrpCat.hom_ext
    apply MonoidHom.ext
    intro x
    apply LocallyConstant.ext
    intro P
    have := hsplit n
    exact congrArg
      (fun f : LocallyConstant (PrimeSpectrum S) (G.level n).rationalPoints =>
        (G.cyclicPointEquiv hsplit n).symm (f P))
      ((G.level n).etalePoints_naturality a x))

/-- Every split height-one tower is naturally isomorphic to the standard Qp/Zp tower. -/
def FiniteEtale.PDivisibleGroup.etaleTowerIso (G : FiniteEtale.PDivisibleGroup k p 1)
    (hsplit : ∀ n, Algebra.IsFiniteSplit k (G.level n).algebra) :
    FiniteEtale.GroupTower.Iso k (G.points k) (FiniteEtale.etaleTower k p) where
  levelIso := G.etaleLevelPointIso hsplit
  compatibility n := by
    apply NatTrans.ext
    funext R
    apply CommGrpCat.hom_ext
    apply MonoidHom.ext
    intro x
    apply LocallyConstant.ext
    intro P
    have := hsplit n
    have := hsplit (n + 1)
    let y := (G.level n).etalePointsMulEquiv R x P
    let a := (G.cyclicPointEquiv hsplit n).symm y
    change (G.cyclicPointEquiv hsplit (n + 1)).symm
        ((G.level (n + 1)).etalePointsMulEquiv R (x ≫ G.inclusion n) P) =
      Multiplicative.ofAdd (FiniteEtale.cyclicInclusion p n a.toAdd)
    apply (G.cyclicPointEquiv hsplit (n + 1)).injective
    rw [MulEquiv.apply_symm_apply]
    have hs := congrArg (fun f : LocallyConstant (PrimeSpectrum R)
      (G.level (n + 1)).rationalPoints => f P)
      (FiniteEtale.FiniteCommGroupScheme.etalePoints_postcomp (G.inclusion n) R x)
    have hg : G.cyclicPointEquiv hsplit n a = y := (G.cyclicPointEquiv hsplit n).apply_symm_apply y
    exact hs.trans ((congrArg (fun z => z ≫ G.inclusion n) hg.symm).trans
      (G.cyclicPointEquiv_compatibility hsplit n a.toAdd))

/-- An étale first level gives the full standard étale tower, naturally on every affine algebra. -/
theorem FiniteEtale.PDivisibleGroup.etale_classification_of_first_split (G : FiniteEtale.PDivisibleGroup k p 1)
    (hfirst : Algebra.IsFiniteSplit k (G.level 1).algebra) :
    Nonempty (FiniteEtale.GroupTower.Iso k (G.points k) (FiniteEtale.etaleTower k p)) :=
  ⟨G.etaleTowerIso (G.split_of_first_split hfirst)⟩

end

end OAI.AlgebraicGeometry.GroupSchemes

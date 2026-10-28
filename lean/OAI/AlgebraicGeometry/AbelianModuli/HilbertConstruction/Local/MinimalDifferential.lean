import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Local.GaussianStep
import Mathlib.Algebra.Category.ModuleCat.Basic
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.RingTheory.Finiteness.Prod

/-! # Minimal Differential -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Local.MinimalDifferential.LocalSectionLifting

noncomputable section

/-! Minimal local differentials and the induction step that accumulates cancelled summands. -/

universe u

variable {R : Type u} [CommRing R] [IsLocalRing R]
    {M N : ModuleCat.{u} R}

/-- A differential expressed as a map vanishing over the residue field and an identity summand. -/
structure LocalMinimalDifferential (f : M →ₗ[R] N) where
  source : ModuleCat.{u} R
  target : ModuleCat.{u} R
  cancelled : ModuleCat.{u} R
  [sourceFinite : Module.Finite R source]
  [sourceFree : Module.Free R source]
  [targetFinite : Module.Finite R target]
  [targetFree : Module.Free R target]
  [cancelledFinite : Module.Finite R cancelled]
  [cancelledFree : Module.Free R cancelled]
  sourceEquiv : (source × cancelled) ≃ₗ[R] M
  targetEquiv : N ≃ₗ[R] (target × cancelled)
  differential : source →ₗ[R] target
  residue_zero : differential.baseChange (IsLocalRing.ResidueField R) = 0
  normal_form : ∀ x, targetEquiv (f (sourceEquiv x)) = (differential x.1, x.2)

attribute [instance] LocalMinimalDifferential.sourceFinite LocalMinimalDifferential.sourceFree
  LocalMinimalDifferential.targetFinite LocalMinimalDifferential.targetFree
  LocalMinimalDifferential.cancelledFinite LocalMinimalDifferential.cancelledFree

def localMinimalDifferentialOfResidueZero
    [Module.Finite R M] [Module.Free R M] [Module.Finite R N] [Module.Free R N]
    (f : M →ₗ[R] N) (hf : f.baseChange (IsLocalRing.ResidueField R) = 0) :
    LocalMinimalDifferential f where
  source := M
  target := N
  cancelled := ModuleCat.of R (Fin 0 → R)
  sourceEquiv := LinearEquiv.prodUnique
  targetEquiv := LinearEquiv.prodUnique.symm
  differential := f
  residue_zero := hf
  normal_form _x := Prod.ext rfl (Subsingleton.elim _ _)

def localMinimalDifferentialStep
    {M₁ N₁ : ModuleCat.{u} R} (f : M →ₗ[R] N) (g : M₁ →ₗ[R] N₁)
    (eM : (M₁ × R) ≃ₗ[R] M) (eN : N ≃ₗ[R] (N₁ × R)) (d : R ≃ₗ[R] R)
    (h : ∀ x, eN (f (eM x)) = (g x.1, d x.2))
    (P : LocalMinimalDifferential g) : LocalMinimalDifferential f where
  source := P.source
  target := P.target
  cancelled := ModuleCat.of R (P.cancelled × R)
  sourceEquiv := (LinearEquiv.prodAssoc R P.source P.cancelled R).symm.trans
    ((P.sourceEquiv.prodCongr (LinearEquiv.refl R R)).trans eM)
  targetEquiv := eN.trans ((P.targetEquiv.prodCongr d.symm).trans
    (LinearEquiv.prodAssoc R P.target P.cancelled R))
  differential := P.differential
  residue_zero := P.residue_zero
  normal_form x := by
    change (LinearEquiv.prodAssoc R P.target P.cancelled R)
      ((P.targetEquiv.prodCongr d.symm)
        (eN (f (eM (P.sourceEquiv (x.1, x.2.1), x.2.2))))) =
        (P.differential x.1, x.2)
    rw [h]
    change ((P.targetEquiv (g (P.sourceEquiv (x.1, x.2.1)))).1,
      ((P.targetEquiv (g (P.sourceEquiv (x.1, x.2.1)))).2, d.symm (d x.2.2))) = _
    rw [P.normal_form]
    simp

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Local.MinimalDifferential.LocalSectionLifting

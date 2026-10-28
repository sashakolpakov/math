import OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.PicardPullback
import OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.FiniteCancellation
import OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.QuotientActionBase
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.PolarizationData
import OAI.ArithmeticGeometry.OrdinaryLocus.Openness.SmoothReduced

/-! # Polarization Comparison -/

namespace OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.PolarizationComparison.Construction

noncomputable section

/-!
Polarization comparison in the native HilbertConstruction model. Pullback uses the dual
map constructed from the actual Picard functor. Its injectivity follows
from finite-kernel rigidity on the connected reduced abelian source.
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj

universe u

open OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.PolarizationData

section AnyBase

variable {S : Scheme.{u}} {g h : ℕ} {A : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g S} {B : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme h S}
variable (p : A.scheme ⟶ B.scheme) [IsMonHom p]
variable (DA : AbelianModuli.HilbertConstruction.Dual.Data.DualAbelianData A) (DB : AbelianModuli.HilbertConstruction.Dual.Data.DualAbelianData B) {δ : Fin h → ℕ}

/-- The literal homomorphism f followed by the target polarization and
the canonical Picard dual of f. -/
def polarizationPullbackHom (pol₁ : AbelianModuli.HilbertConstruction.PolarizationData.Polarization DB δ) : A.scheme ⟶ DA.abelian.scheme :=
  p ≫ pol₁.isogeny.hom ≫ PicardPullback.Construction.IntrinsicPicardPullback.dualMap p DA DB

/-- The polarization record is determined by its actual morphism. -/
theorem polarization_ext (pol₁ pol₂ : AbelianModuli.HilbertConstruction.PolarizationData.Polarization DB δ) (h : pol₁.isogeny.hom = pol₂.isogeny.hom) : pol₁ = pol₂ := by
  cases pol₁ with
  | mk l hl hpos =>
    cases pol₂ with
    | mk m hm hpos' =>
      cases l
      cases m
      cases h
      rfl

end AnyBase

variable {K : Type u} [Field K] [IsAlgClosed K] {g h : ℕ}
variable {A : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g (Spec (.of K))} {B : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme h (Spec (.of K))}
variable (p : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme.Isogeny A B) (DA : AbelianModuli.HilbertConstruction.Dual.Data.DualAbelianData A) (DB : AbelianModuli.HilbertConstruction.Dual.Data.DualAbelianData B)
variable {δ : Fin h → ℕ}

/-- Once the canonical dual is a finite group map, equality after
isogeny pullback determines the entire native polarization record. -/
theorem polarization_eq_of_pullback_eq
    [IsMonHom (PicardPullback.Construction.IntrinsicPicardPullback.dualMap p.hom DA DB)]
    [IsFinite (PicardPullback.Construction.IntrinsicPicardPullback.dualMap p.hom DA DB).left]
    (pol₁ pol₂ : AbelianModuli.HilbertConstruction.PolarizationData.Polarization DB δ)
    (h : polarizationPullbackHom p.hom DA DB pol₁ = polarizationPullbackHom p.hom DA DB pol₂) : pol₁ = pol₂ := by
  have : IsReduced B.scheme.left := ArithmeticGeometry.OrdinaryLocus.Openness.SmoothReduced.Construction.isReduced_smooth_over_field B.scheme.hom
  have : ConnectedSpace B.scheme.left :=
    GeometricallyConnected.connectedSpace_of_subsingleton B.scheme.hom
  have : EffectiveEpi p.hom := PELModuli.IntegralModel.IsogenyFactorizationIs.IsogenyFactorization.effectiveEpi_over_of_fpqc p.hom
  apply polarization_ext DB pol₁ pol₂
  exact FiniteCancellation.Construction.polarizationPullback_injective p.hom (PicardPullback.Construction.IntrinsicPicardPullback.dualMap p.hom DA DB)
    pol₁.isogeny.hom pol₂.isogeny.hom h

end

end OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.PolarizationComparison.Construction

import OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.QuotientRosati
import OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Field.DualPicardKernel
import OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Field.PoincarePullback
import OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Field.FiniteKernelCancellation
import OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.PicardAdjoints

/-! # Rosati -/

namespace OAI.AlgebraicGeometry.Isogenies.NeighborCounting.FieldQuotient.Rosati

noncomputable section

/-! The target Rosati morphism equation follows from the actual
source equation and a quotient polarization's pullback identity.
No target Rosati compatibility is assumed. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj

universe v

variable {k : Type} [Field k] {g : ℕ}
variable {A : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g (Spec (.of k))} {B : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g (Spec (.of k))}
variable (f : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme.Isogeny A B)
variable (DA : AbelianModuli.HilbertConstruction.Dual.Data.DualAbelianData A) (DB : AbelianModuli.HilbertConstruction.Dual.Data.DualAbelianData B)
variable {δA : Fin g → ℕ} {δB : Fin g → ℕ}
variable (polA : AbelianModuli.HilbertConstruction.PolarizationData.Polarization DA δA) (polB : AbelianModuli.HilbertConstruction.PolarizationData.Polarization DB δB)
variable {O : Type v} [CommRing O]
variable (ρ : AbelianModuli.ReferenceFamily.ActionData.IntegralAction O A) (σ : AbelianModuli.ReferenceFamily.ActionData.IntegralAction O B)
variable (hσ : ∀ a : O, ρ.map a ≫ f.hom = f.hom ≫ σ.map a)

include hσ in
/-- A quotient polarization inherits the original conjugate-action
equation. Finiteness of the canonical dual is derived from the isogeny. -/
theorem quotient_rosati_canonicalDual (m : ℕ)
    (hpol : AbelianScheme.FrobeniusKernel.PolarizationComparison.Construction.polarizationPullbackHom f.hom DA DB polB = polA.isogeny.hom ^ m)
    (a b : O)
    (hsource : polA.isogeny.hom ≫ AbelianScheme.FrobeniusKernel.PicardPullback.Construction.IntrinsicPicardPullback.dualMap (ρ.map a) DA DA =
      ρ.map b ≫ polA.isogeny.hom) :
    polB.isogeny.hom ≫ AbelianScheme.FrobeniusKernel.PicardPullback.Construction.IntrinsicPicardPullback.dualMap (σ.map a) DB DB =
      σ.map b ≫ polB.isogeny.hom := by
  have : IsMonHom (AbelianScheme.FrobeniusKernel.PicardPullback.Construction.IntrinsicPicardPullback.dualMap f.hom DA DB) :=
    NeighborCounting.Field.PoincarePullback.nativeDualMap_isMonHom DA DB f.hom
  have : IsMonHom (AbelianScheme.FrobeniusKernel.PicardPullback.Construction.IntrinsicPicardPullback.dualMap (ρ.map a) DA DA) :=
    NeighborCounting.Field.PoincarePullback.nativeDualMap_isMonHom DA DA (ρ.map a)
  have : IsMonHom (AbelianScheme.FrobeniusKernel.PicardPullback.Construction.IntrinsicPicardPullback.dualMap (σ.map a) DB DB) :=
    NeighborCounting.Field.PoincarePullback.nativeDualMap_isMonHom DB DB (σ.map a)
  have : IsFinite (AbelianScheme.FrobeniusKernel.PicardPullback.Construction.IntrinsicPicardPullback.dualMap f.hom DA DB).left := by
    rw [AbelianScheme.FrobeniusKernel.Polarization.Construction.NativePicardPullback.dualMap_eq_e57]
    exact NeighborCounting.Field.DualPicardKernel.fieldDualPicardPullback_finite DA DB f
  have : EffectiveEpi f.hom := PELModuli.IntegralModel.IsogenyFactorizationIs.IsogenyFactorization.effectiveEpi_over_of_fpqc f.hom
  have hd := AbelianScheme.FrobeniusKernel.QuotientRosati.Construction.quotientAction_dual_square f DA DB ρ σ hσ a
  have hpower : (polA.isogeny.hom ^ m) ≫ AbelianScheme.FrobeniusKernel.PicardPullback.Construction.IntrinsicPicardPullback.dualMap (ρ.map a) DA DA =
      ρ.map b ≫ polA.isogeny.hom ^ m := by
    rw [MonObj.pow_comp, hsource, MonObj.comp_pow]
  apply NeighborCounting.Field.FiniteKernelCancellation.cancel_finite_group_map B
    (AbelianScheme.FrobeniusKernel.PicardPullback.Construction.IntrinsicPicardPullback.dualMap f.hom DA DB)
  apply (cancel_epi f.hom).mp
  change f.hom ≫ polB.isogeny.hom ≫ AbelianScheme.FrobeniusKernel.PicardPullback.Construction.IntrinsicPicardPullback.dualMap f.hom DA DB =
    polA.isogeny.hom ^ m at hpol
  simp only [Category.assoc]
  rw [hd, ← Category.assoc polB.isogeny.hom, ← Category.assoc f.hom, hpol,
    hpower, ← hpol, ← Category.assoc (ρ.map b) f.hom, hσ b, Category.assoc]

end

end OAI.AlgebraicGeometry.Isogenies.NeighborCounting.FieldQuotient.Rosati

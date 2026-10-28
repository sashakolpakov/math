import OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.IsogenyPolarizationUniqueness
import OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.PicardAdjoints

/-! # Quotient Rosati -/

namespace OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.QuotientRosati.Construction

noncomputable section

/-! The target Rosati morphism equation follows from the actual
source equation and a quotient polarization's pullback identity.
No target Rosati compatibility is assumed. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj

universe u v

variable {k : Type u} [Field k] [IsAlgClosed k] {g h : ℕ}
variable {A : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g (Spec (.of k))} {B : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme h (Spec (.of k))}
variable (f : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme.Isogeny A B)
variable (DA : AbelianModuli.HilbertConstruction.Dual.Data.DualAbelianData A) (DB : AbelianModuli.HilbertConstruction.Dual.Data.DualAbelianData B)
variable {δA : Fin g → ℕ} {δB : Fin h → ℕ}
variable (polA : AbelianModuli.HilbertConstruction.PolarizationData.Polarization DA δA) (polB : AbelianModuli.HilbertConstruction.PolarizationData.Polarization DB δB)
variable {O : Type v} [CommRing O]
variable (ρ : AbelianModuli.ReferenceFamily.ActionData.IntegralAction O A) (σ : AbelianModuli.ReferenceFamily.ActionData.IntegralAction O B)
variable (hσ : ∀ a : O, ρ.map a ≫ f.hom = f.hom ≫ σ.map a)

include hσ in
omit [IsAlgClosed k] in
theorem quotientAction_dual_square (a : O) :
    PicardPullback.Construction.IntrinsicPicardPullback.dualMap (σ.map a) DB DB ≫ PicardPullback.Construction.IntrinsicPicardPullback.dualMap f.hom DA DB =
      PicardPullback.Construction.IntrinsicPicardPullback.dualMap f.hom DA DB ≫ PicardPullback.Construction.IntrinsicPicardPullback.dualMap (ρ.map a) DA DA := by
  simp only [← PicardPullback.Construction.IntrinsicPicardPullback.dualMap_comp, hσ a]

include hσ in
/-- A quotient polarization inherits the original conjugate-action
equation. Finiteness of the canonical dual is derived from the isogeny. -/
theorem quotient_rosati_canonicalDual (m : ℕ)
    (hpol : PolarizationComparison.Construction.polarizationPullbackHom f.hom DA DB polB = polA.isogeny.hom ^ m)
    (a b : O)
    (hsource : polA.isogeny.hom ≫ PicardPullback.Construction.IntrinsicPicardPullback.dualMap (ρ.map a) DA DA =
      ρ.map b ≫ polA.isogeny.hom) :
    polB.isogeny.hom ≫ PicardPullback.Construction.IntrinsicPicardPullback.dualMap (σ.map a) DB DB =
      σ.map b ≫ polB.isogeny.hom := by
  have : IsFinite (PicardPullback.Construction.IntrinsicPicardPullback.dualMap f.hom DA DB).left := IsogenyPolarizationUniqueness.Construction.isogeny_dualMap_finite f DA DB
  have : IsReduced B.scheme.left := ArithmeticGeometry.OrdinaryLocus.Openness.SmoothReduced.Construction.isReduced_smooth_over_field B.scheme.hom
  have : ConnectedSpace B.scheme.left :=
    GeometricallyConnected.connectedSpace_of_subsingleton B.scheme.hom
  have : EffectiveEpi f.hom := PELModuli.IntegralModel.IsogenyFactorizationIs.IsogenyFactorization.effectiveEpi_over_of_fpqc f.hom
  have hd := quotientAction_dual_square f DA DB ρ σ hσ a
  have hpower : (polA.isogeny.hom ^ m) ≫ PicardPullback.Construction.IntrinsicPicardPullback.dualMap (ρ.map a) DA DA =
      ρ.map b ≫ polA.isogeny.hom ^ m := by
    rw [MonObj.pow_comp, hsource, MonObj.comp_pow]
  apply FiniteCancellation.Construction.polarizationPullback_injective f.hom (PicardPullback.Construction.IntrinsicPicardPullback.dualMap f.hom DA DB)
  change f.hom ≫ polB.isogeny.hom ≫ PicardPullback.Construction.IntrinsicPicardPullback.dualMap f.hom DA DB =
    polA.isogeny.hom ^ m at hpol
  simp only [Category.assoc]
  rw [hd, ← Category.assoc polB.isogeny.hom, ← Category.assoc f.hom, hpol,
    hpower, ← hpol, ← Category.assoc (ρ.map b) f.hom, hσ b, Category.assoc]

end

end OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.QuotientRosati.Construction

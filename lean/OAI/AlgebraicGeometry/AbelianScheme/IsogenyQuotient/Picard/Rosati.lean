import OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.QuotientRosati
import OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.IntrinsicPoincare

/-! # Rosati -/

namespace OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Picard.Rosati.Construction

noncomputable section

/-! Over a geometric field, the constructed quotient Picard isogeny
inherits the actual conjugate-action equation. Positivity of that map
is not used in finite-kernel cancellation. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj

open OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.QuotientRosati.Construction

universe u v

variable {k : Type u} [Field k] [IsAlgClosed k] {g d : ℕ}
  {A : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g (Spec (.of k))} {B : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme d (Spec (.of k))}
  (DA : AbelianModuli.HilbertConstruction.Dual.Data.DualAbelianData A) (DB : AbelianModuli.HilbertConstruction.Dual.Data.DualAbelianData B)
  (f : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme.Isogeny A B)
  (ell : A.scheme ⟶ DA.abelian.scheme)
  (m : B.scheme ⟶ DB.abelian.scheme) [IsMonHom m]
  {R : Type v} [CommRing R]
  (ρ : AbelianModuli.ReferenceFamily.ActionData.IntegralAction R A) (σ : AbelianModuli.ReferenceFamily.ActionData.IntegralAction R B)
  (hσ : ∀ a : R, ρ.map a ≫ f.hom = f.hom ≫ σ.map a)

include hσ in
theorem picardQuotient_rosati_equation (n : ℕ)
    (hp : f.hom ≫ m ≫ FrobeniusKernel.PicardPullback.Construction.IntrinsicPicardPullback.dualMap f.hom DA DB = ell ^ n)
    (a b : R)
    (hsource : ell ≫ FrobeniusKernel.PicardPullback.Construction.IntrinsicPicardPullback.dualMap (ρ.map a) DA DA = ρ.map b ≫ ell) :
    m ≫ FrobeniusKernel.PicardPullback.Construction.IntrinsicPicardPullback.dualMap (σ.map a) DB DB = σ.map b ≫ m := by
  have : IsFinite (FrobeniusKernel.PicardPullback.Construction.IntrinsicPicardPullback.dualMap f.hom DA DB).left := FrobeniusKernel.IsogenyPolarizationUniqueness.Construction.isogeny_dualMap_finite f DA DB
  have : IsReduced B.scheme.left := ArithmeticGeometry.OrdinaryLocus.Openness.SmoothReduced.Construction.isReduced_smooth_over_field B.scheme.hom
  have : ConnectedSpace B.scheme.left := GeometricallyConnected.connectedSpace_of_subsingleton B.scheme.hom
  have : EffectiveEpi f.hom := PELModuli.IntegralModel.IsogenyFactorizationIs.IsogenyFactorization.effectiveEpi_over_of_fpqc f.hom
  have hd := FrobeniusKernel.QuotientRosati.Construction.quotientAction_dual_square f DA DB ρ σ hσ a
  have hpower : (ell ^ n) ≫ FrobeniusKernel.PicardPullback.Construction.IntrinsicPicardPullback.dualMap (ρ.map a) DA DA = ρ.map b ≫ ell ^ n := by
    rw [MonObj.pow_comp, hsource, MonObj.comp_pow]
  apply FrobeniusKernel.FiniteCancellation.Construction.polarizationPullback_injective f.hom (FrobeniusKernel.PicardPullback.Construction.IntrinsicPicardPullback.dualMap f.hom DA DB)
  simp only [Category.assoc]
  rw [hd, ← Category.assoc m, ← Category.assoc f.hom, hp, hpower, ← hp,
    ← Category.assoc (ρ.map b) f.hom, hσ b, Category.assoc]

end

end OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Picard.Rosati.Construction

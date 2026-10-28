import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Canonical.PicardImage
import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Canonical.PicardImageDualData
import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Picard.DualDimension

/-! # Dual Existence -/

namespace OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Canonical.DualExistence.Construction

noncomputable section

/-! The original polarized abelian variety and the full canonical
isotropic quotient kernel construct the quotient's bundled dual abelian data. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj BigOperators

attribute [local instance] Picard.PoincareBundle.Product.Noetherian.product_finiteType Picard.PoincareBundle.Product.Noetherian.product_noetherian

variable {S : Scheme} {g : ℕ} {A : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g S}
  (D : AbelianModuli.HilbertConstruction.Dual.Data.DualAbelianData A) {δ : Fin g → ℕ} (pol : AbelianModuli.HilbertConstruction.PolarizationData.Polarization D δ)
  (k : Type) [Field k] [IsAlgClosed k] (s : Spec (.of k) ⟶ S) (n : ℕ) (hn : 0 < n)
  {B : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g (Spec (.of k))} (f : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme.Isogeny (A.pullback s) B)
  (hker : ∀ (T : Over (Spec (.of k))) (x : T ⟶ (A.pullback s).scheme), x ≫ f.hom = 1 → x ^ n = 1)
  (hlag :
    let F := SubgroupTransport.Construction.relativeSubgroupPullback (Torsion.Groups.Construction.nativeTorsionInclusion (A.pullback s).scheme n) (Intrinsic.MorphismKernel.Construction.nativeMorphismKernel f.hom)
    (IsogenyQuotient.Field.PolarizationAdapter.Construction.fieldNativePolarizationPairing (A.pullback s) (D.pullback s) (pol.pullback s) n hn).relativeAnnihilator F = F)

include D pol s n hn f hker hlag in
set_option backward.isDefEq.respectTransparency false in
theorem geometricCanonicalQuotientDual_nonempty (hc : Nat.Coprime n ((∏ j, δ j) ^ 2)) :
    Nonempty (AbelianModuli.HilbertConstruction.Dual.Data.DualAbelianData B) := by
  have : GeometricallyIntegral B.scheme.hom := Quotients.FiniteDescent.AbelianGeometric.Construction.AbelianGeometricIntegral.geometricallyIntegral B.scheme
  have : IsLocallyNoetherian B.scheme.left := LocallyOfFiniteType.isLocallyNoetherian B.scheme.hom
  obtain ⟨C, q, i, hq, hfin, hsurj, hmono, hfac⟩ :=
    PicardImage.Construction.geometricCanonicalQuotientPicard_abelian_image D pol k s n hn f.hom hker hlag
  have : IsMonHom q := hq
  have : IsFinite q.left := hfin.1
  have : Flat q.left := hfin.2.1
  have : LocallyOfFinitePresentation q.left := hfin.2.2
  have : Surjective q.left := hsurj
  have : Mono i := hmono
  let DB := PicardImageDualData.Construction.geometricCanonicalPicardImageDualData D pol k s n hn f.hom hker hlag q i hfac hc
  exact ⟨Picard.DualDimension.Construction.picardDualWithDimension B DB q⟩

end

end OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Canonical.DualExistence.Construction

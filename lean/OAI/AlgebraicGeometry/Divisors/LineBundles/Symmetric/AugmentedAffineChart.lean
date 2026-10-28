import OAI.AlgebraicGeometry.Divisors.LineBundles.Symmetric.AffineSchemeIso
import OAI.AlgebraicGeometry.Divisors.LineBundles.SymmetricInfinity.Inclusion

/-! # Augmented Affine Chart -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.Symmetric.AugmentedAffineChart.BundleCycles

noncomputable section

/-! A module basis gives the actual affine-space open complementary
to the distinguished infinity hyperplane of its augmented Proj. -/

open _root_.AlgebraicGeometry _root_.CategoryTheory

variable {R M ι : Type} [CommRing R] [AddCommGroup M] [Module R M]
    (basis : Module.Basis ι R M)

def symmetricAugmentedAffineChart :
    AffineSpace ι (Spec (.of R)) ⟶ SymmetricProjective.Scheme.BundleCycles.symmetricProjectiveScheme R (R × M) :=
  (AffineSchemeIso.BundleCycles.symmetricAffineSchemeIso basis).inv ≫ AffineCompactification.BundleCycles.symmetricAffineCompactification R M

instance symmetricAugmentedAffineChart_isOpenImmersion : IsOpenImmersion (symmetricAugmentedAffineChart basis) := by
  unfold symmetricAugmentedAffineChart
  infer_instance

theorem symmetricAugmentedAffineChart_over :
    symmetricAugmentedAffineChart basis ≫ SymmetricProjective.Scheme.BundleCycles.symmetricProjectiveToBase R (R × M) =
      (AffineSpace ι (Spec (.of R)) ↘ Spec (.of R)) := by
  unfold symmetricAugmentedAffineChart
  rw [Category.assoc, AffineCompactification.BundleCycles.symmetricAffineCompactification_over, ← AffineSchemeIso.BundleCycles.symmetricAffineSchemeIso_over basis,
    Iso.inv_hom_id_assoc]

theorem symmetricAugmentedAffineChart_complement :
    Set.range (SymmetricInfinity.Inclusion.BundleCycles.symmetricInfinityInclusion R M) = (Set.range (symmetricAugmentedAffineChart basis))ᶜ := by
  have he : (symmetricAugmentedAffineChart basis).opensRange = (AffineCompactification.BundleCycles.symmetricAffineCompactification R M).opensRange :=
    Scheme.Hom.opensRange_comp_of_isIso _ _
  have hr : Set.range (symmetricAugmentedAffineChart basis) = Set.range (AffineCompactification.BundleCycles.symmetricAffineCompactification R M) :=
    congrArg (fun U : (SymmetricProjective.Scheme.BundleCycles.symmetricProjectiveScheme R (R × M)).Opens =>
      (U : Set (SymmetricProjective.Scheme.BundleCycles.symmetricProjectiveScheme R (R × M)))) he
  rw [hr]
  exact SymmetricInfinity.Inclusion.BundleCycles.symmetricInfinityInclusion_range R M

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.Symmetric.AugmentedAffineChart.BundleCycles

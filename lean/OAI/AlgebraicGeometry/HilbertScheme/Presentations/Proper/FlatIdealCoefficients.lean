import OAI.AlgebraicGeometry.HilbertScheme.Presentations.GenericSourceIdealCoefficients
import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Proper.AffineCoefficientProperty
import OAI.AlgebraicGeometry.HilbertScheme.Presentations.ZeroBaseCoefficients
import OAI.AlgebraicGeometry.HilbertScheme.Presentations.ProductCoefficientAssembly
import OAI.AlgebraicGeometry.HilbertScheme.Presentations.FaithfullyFlatCoefficientDescent
import OAI.AlgebraicGeometry.HilbertScheme.Presentations.LocalizationCompletionCover
import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Noetherian.QuotientInduction

/-! # Flat Ideal Coefficients -/

namespace OAI.AlgebraicGeometry.HilbertScheme.Presentations.Proper.FlatIdealCoefficients

noncomputable section

/-! Every ideal on a proper flat source over a Noetherian affine base
has a coefficient ideal, with no projectivity assumption on the source. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

universe u

theorem proper_flat_ideal_coefficients (R : CommRingCat.{u}) [IsNoetherianRing R] :
    AffineCoefficientProperty.ProperAffineCoefficientProperty R := by
  apply Noetherian.QuotientInduction.noetherian_quotient_induction R AffineCoefficientProperty.ProperAffineCoefficientProperty
  intro A _ hquot
  rcases subsingleton_or_nontrivial A with hzero | hnonzero
  · let : Subsingleton A := hzero
    exact ZeroBaseCoefficients.properAffineCoefficientProperty_zero A
  · let : Nontrivial A := hnonzero
    intro X f _ _ K
    let : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace f
    obtain ⟨s, hs, hgeneric⟩ := GenericSourceIdealCoefficients.exists_generic_source_ideal_coefficients A f
    let L := CommRingCat.of (Localization.Away s)
    let H := CommRingCat.of (AdicCompletion (Ideal.span {s}) A)
    let φL : A ⟶ L := CommRingCat.ofHom (algebraMap A L)
    let φH : A ⟶ H := CommRingCat.ofHom (algebraMap A H)
    obtain ⟨I, hI⟩ := hgeneric (K.comap (pullback.fst f (Spec.map φL)))
    have hcomplete := AffineCoefficientProperty.properAffineCoefficientProperty_principalCompletion A s hs hquot
    obtain ⟨J, hJ⟩ := hcomplete (pullback f (Spec.map φH))
      (pullback.snd f (Spec.map φH)) (K.comap (pullback.fst f (Spec.map φH)))
    let C := CommRingCat.of (L × H)
    let : Module.FaithfullyFlat A C := LocalizationCompletionCover.localization_completion_faithfullyFlat A s
    have hC := ProductCoefficientAssembly.affineIdealCoefficient_product_assembly A L H f K I J hI hJ
    exact ⟨(I.prod J).comap (algebraMap A C),
      FaithfullyFlatCoefficientDescent.affineIdealCoefficient_faithfullyFlat_descent A C f K (I.prod J) hC⟩

end

end OAI.AlgebraicGeometry.HilbertScheme.Presentations.Proper.FlatIdealCoefficients

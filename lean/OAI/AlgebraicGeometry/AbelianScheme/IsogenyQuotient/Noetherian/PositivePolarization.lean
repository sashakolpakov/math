import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Noetherian.DualComplement
import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.PolarizationAssembly
import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Canonical.StandardWeilIsotropy
import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.SharedDualMapComparison
import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.ParameterKernel
import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Torsion.Construction
import OAI.AlgebraicGeometry.Picard.PoincareBundle.Canonical.WeilPolarizationDescent

/-! # Positive Polarization -/

namespace OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Noetherian.PositivePolarization.Construction

noncomputable section

/-! Actual geometric PoincareBundle polarizations assemble into the relative
positive HilbertConstruction polarization of unchanged type over a Noetherian base. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj BigOperators

variable {S : Scheme.{0}} [IsLocallyNoetherian S] {g : ℕ} {A B : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g S}
  (DA : AbelianModuli.HilbertConstruction.Dual.Data.DualAbelianData A) (DB : AbelianModuli.HilbertConstruction.Dual.Data.DualAbelianData B)
  {δ : Fin g → ℕ} (pol : AbelianModuli.HilbertConstruction.PolarizationData.Polarization DA δ)
  (f : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme.Isogeny A B) (v : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme.Isogeny B A) (n : ℕ) (hn : 0 < n)
  (hfv : f.hom ≫ v.hom = (𝟙 A.scheme) ^ n)
  (hvf : v.hom ≫ f.hom = (𝟙 B.scheme) ^ n)
  (hf : ∀ (U : Over S) (x : U ⟶ Picard.Homomorphisms.Kernel.Construction.kernelScheme f.hom), x ^ n = 1)
  (hlag : ∀ (K : Type) [Field K] [IsAlgClosed K] (s : Spec (.of K) ⟶ S),
    let H := SubgroupTransport.Construction.relativeSubgroupPullback (Torsion.Groups.Construction.nativeTorsionInclusion (A.pullback s).scheme n)
      (Intrinsic.MorphismKernel.Construction.nativeMorphismKernel (f.pullback s).hom)
    (IsogenyQuotient.Field.PolarizationAdapter.Construction.fieldNativePolarizationPairing (A.pullback s) (DA.pullback s) (pol.pullback s) n hn).relativeAnnihilator H = H)
  (hc : Nat.Coprime n ((∏ j, δ j) ^ 2))

include hfv hvf hf hlag hc in
set_option backward.isDefEq.respectTransparency false in
theorem noetherian_relative_positive_polarization
    {k : Type} [Field k] [CharZero k] (base : S ⟶ Spec (.of k)) :
    ∃! p : AbelianModuli.HilbertConstruction.PolarizationData.Polarization DB δ,
      f.hom ≫ p.isogeny.hom ≫ FrobeniusKernel.PicardPullback.Construction.IntrinsicPicardPullback.dualMap f.hom DA DB = pol.isogeny.hom ^ n := by
  have : IsMonHom (FrobeniusKernel.PicardPullback.Construction.IntrinsicPicardPullback.dualMap f.hom DA DB) := DualMaps.Construction.noetherian_nativeDualMap_isMonHom f.hom DA DB
  have : IsMonHom (FrobeniusKernel.PicardPullback.Construction.IntrinsicPicardPullback.dualMap v.hom DB DA) := DualMaps.Construction.noetherian_nativeDualMap_isMonHom v.hom DB DA
  obtain ⟨hd₁, hd₂⟩ := DualComplement.Construction.noetherian_nativeDualMap_complements DA DB f v n hfv hvf
  apply PolarizationAssembly.Construction.relative_polarization_from_field_polarizations base A B DA DB δ pol n hn f v.hom
    (FrobeniusKernel.PicardPullback.Construction.IntrinsicPicardPullback.dualMap f.hom DA DB) (FrobeniusKernel.PicardPullback.Construction.IntrinsicPicardPullback.dualMap v.hom DB DA) hfv hd₁ hd₂ Torsion.Construction.verified_TorsionQuotientInput
  intro K _ _ s
  let hk := ParameterKernel.Construction.isogeny_baseChange_kernelPoint_pow f n hf s
  have hl := Canonical.StandardWeilIsotropy.Construction.canonicalKernel_standardWeil_selfAnnihilating (DA.pullback s) (pol.pullback s)
    n hn (f.pullback s).hom hk (hlag K s)
  obtain ⟨p, hp, _hu⟩ := Picard.PoincareBundle.Canonical.WeilPolarizationDescent.existsUnique_polarization
    (DA.pullback s) (DB.pullback s) (pol.pullback s) (f.pullback s) n hn hc hk hl
  rw [SharedDualMapComparison.Construction.e45SharedDualMap_eq_native] at hp
  refine ⟨p, ?_⟩
  rw [FrobeniusKernel.DualMapBaseChange.Construction.NativePicardPullback.dualMap_baseChange]
  exact hp

end

end OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Noetherian.PositivePolarization.Construction

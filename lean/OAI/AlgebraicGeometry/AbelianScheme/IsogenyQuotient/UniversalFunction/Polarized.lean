import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.UniversalFunction.IsotropicDual
import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.UniversalFunction.PositivePolarization
import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.ScalarComplement

/-! # Polarized -/

namespace OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.UniversalFunction.Polarized.Construction

noncomputable section

/-! Full positive polarization on the actual isotropic
quotient, constructing its dual and scalar complement from the original source. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj BigOperators

variable {S : Scheme.{0}} {g : ℕ} {A B : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g S}
  (D : AbelianModuli.HilbertConstruction.Dual.Data.DualAbelianData A) (hA : GlobalFunctions.Construction.HasUniversalGlobalFunctions A.scheme) {δ : Fin g → ℕ} (pol : AbelianModuli.HilbertConstruction.PolarizationData.Polarization D δ)
  (f : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme.Isogeny A B) (n : ℕ) (hn : 0 < n)
  (hf : ∀ (U : Over S) (x : U ⟶ Picard.Homomorphisms.Kernel.Construction.kernelScheme f.hom), x ^ n = 1)
  (hlag : ∀ (K : Type) [Field K] [IsAlgClosed K] (s : Spec (.of K) ⟶ S),
    let H := SubgroupTransport.Construction.relativeSubgroupPullback (Torsion.Groups.Construction.nativeTorsionInclusion (A.pullback s).scheme n)
      (Intrinsic.MorphismKernel.Construction.nativeMorphismKernel (f.pullback s).hom)
    (IsogenyQuotient.Field.PolarizationAdapter.Construction.fieldNativePolarizationPairing (A.pullback s) (D.pullback s) (pol.pullback s) n hn).relativeAnnihilator H = H)
  (hc : Nat.Coprime n ((∏ j, δ j) ^ 2))

include hA hf hlag hc in
set_option backward.isDefEq.respectTransparency false in
theorem universalFunction_isotropic_quotient_polarization_exists
    {k : Type} [Field k] [CharZero k] (base : S ⟶ Spec (.of k)) :
    ∃ DB : AbelianModuli.HilbertConstruction.Dual.Data.DualAbelianData B, GlobalFunctions.Construction.HasUniversalGlobalFunctions DB.abelian.scheme ∧
      ∃ p : AbelianModuli.HilbertConstruction.PolarizationData.Polarization DB δ,
      f.hom ≫ p.isogeny.hom ≫ FrobeniusKernel.PicardPullback.Construction.IntrinsicPicardPullback.dualMap f.hom D DB = pol.isogeny.hom ^ n := by
  obtain ⟨v, hfv, hvf, hv⟩ := ScalarComplement.Construction.exists_isogeny_scalar_complement f n hn hf base
  obtain ⟨DB, hDB⟩ := IsotropicDual.Construction.canonicalIsotropicUniversalQuotientDual_exists D hA pol f v n hn hf hv hlag hc base
  have hD := GlobalFunctions.Construction.universalGlobalFunctions_of_finiteFlat_source pol.isogeny.hom hA
  obtain ⟨p, hp, _hu⟩ := PositivePolarization.Construction.universalFunction_relative_positive_polarization D DB hD hDB pol f v n hn hfv hvf hf hlag hc base
  exact ⟨DB, hDB, p, hp⟩

end

end OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.UniversalFunction.Polarized.Construction

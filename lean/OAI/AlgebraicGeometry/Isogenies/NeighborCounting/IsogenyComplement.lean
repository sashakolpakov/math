import OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.QuotientAction
import OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.IsogenyPolarizationUniqueness
import OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.PicardAdjoints
import OAI.AlgebraicGeometry.PELModuli.CMPoints.BlocksProjectors

/-! # Isogeny Complement -/

namespace OAI.AlgebraicGeometry.Isogenies.NeighborCounting.IsogenyComplement

noncomputable section

/-! Construct the complementary map of an isogeny from its actual
kernel bound. Its polarization-adjoint equation follows from the
given multiplier and the original PEL Rosati condition. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj

attribute [local instance] Picard.Homomorphisms.GroupDescent.Construction.groupHom_pow_isMonHom

variable {S : Scheme} {g h : ℕ} {A : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g S} {B : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme h S}
variable (f : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme.Isogeny A B) (n : ℕ)
variable (hk : ∀ (T : Over S) (a : T ⟶ A.scheme), a ≫ f.hom = 1 → a ^ n = 1)

include hk in
theorem isogeny_complement_exists :
    ∃! c : B.scheme ⟶ A.scheme, IsMonHom c ∧ f.hom ≫ c = (𝟙 A.scheme) ^ n := by
  apply Picard.PoincareBundle.Epi.Construction.fpqc_group_hom_descent f.hom ((𝟙 A.scheme) ^ n)
  intro T a ha
  rw [MonObj.comp_pow, Category.comp_id]
  exact hk T a ha

def isogenyComplement : B.scheme ⟶ A.scheme :=
  Classical.choose (isogeny_complement_exists f n hk)

instance isogenyComplement_isMonHom : IsMonHom (isogenyComplement f n hk) :=
  (Classical.choose_spec (isogeny_complement_exists f n hk)).1.1

theorem isogenyComplement_projection : f.hom ≫ isogenyComplement f n hk = (𝟙 A.scheme) ^ n :=
  (Classical.choose_spec (isogeny_complement_exists f n hk)).1.2

theorem isogenyComplement_reverse : isogenyComplement f n hk ≫ f.hom = (𝟙 B.scheme) ^ n := by
  have : EffectiveEpi f.hom := Picard.PoincareBundle.Epi.Construction.effectiveEpi_over_of_fpqc f.hom
  apply (cancel_epi f.hom).mp
  rw [← Category.assoc, isogenyComplement_projection, MonObj.pow_comp, MonObj.comp_pow,
    Category.id_comp, Category.comp_id]

variable {k : Type} [Field k] [IsAlgClosed k] {N M : ℕ} {δ : Fin g → ℕ} {ε : Fin h → ℕ}
variable (PA : AbelianModuli.HilbertConstruction.PolarizationData.PolarizedAbelianWithFullLevel g δ N (Spec (.of k)))
variable (PB : AbelianModuli.HilbertConstruction.PolarizationData.PolarizedAbelianWithFullLevel h ε M (Spec (.of k)))
variable {E : Type} [Field E] [NumberField E] [NumberField.IsCMField E]
variable (ρ : AbelianModuli.ReferenceFamily.ActionData.IntegralAction (NumberField.RingOfIntegers E) PA.abelian)
variable (hρ : AbelianModuli.ReferenceFamily.ActionData.RosatiConjugation PA ρ)

include hρ in
omit [IsAlgClosed k] in
theorem polarization_scalar_dual (n : ℕ) :
    PA.polarization.isogeny.hom ≫ AbelianScheme.FrobeniusKernel.PicardPullback.Construction.IntrinsicPicardPullback.dualMap ((𝟙 PA.abelian.scheme) ^ n) PA.dual PA.dual =
      PA.polarization.isogeny.hom ^ n := by
  have h := AbelianScheme.FrobeniusKernel.PicardAdjoints.Construction.rosati_canonicalDual PA ρ hρ (n : NumberField.RingOfIntegers E)
  simpa only [map_natCast, PELModuli.CMPoints.BlocksProjectors.integralAction_natCast, MonObj.pow_comp, Category.id_comp] using h

variable (f : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme.Isogeny PA.abelian PB.abelian) (m : ℕ)
variable (hk : ∀ (T : Over (Spec (.of k))) (a : T ⟶ PA.abelian.scheme), a ≫ f.hom = 1 → a ^ m = 1)

include hρ in
theorem isogenyComplement_polarization_adjoint
    (hpol : AbelianScheme.FrobeniusKernel.PolarizationComparison.Construction.polarizationPullbackHom f.hom PA.dual PB.dual PB.polarization = PA.polarization.isogeny.hom ^ m) :
    PA.polarization.isogeny.hom ≫ AbelianScheme.FrobeniusKernel.PicardPullback.Construction.IntrinsicPicardPullback.dualMap (isogenyComplement f m hk) PB.dual PA.dual =
      f.hom ≫ PB.polarization.isogeny.hom := by
  have : IsFinite (AbelianScheme.FrobeniusKernel.PicardPullback.Construction.IntrinsicPicardPullback.dualMap f.hom PA.dual PB.dual).left :=
    AbelianScheme.FrobeniusKernel.IsogenyPolarizationUniqueness.Construction.isogeny_dualMap_finite f PA.dual PB.dual
  have : IsReduced PA.abelian.scheme.left := ArithmeticGeometry.OrdinaryLocus.Openness.SmoothReduced.Construction.isReduced_smooth_over_field PA.abelian.scheme.hom
  have : ConnectedSpace PA.abelian.scheme.left :=
    GeometricallyConnected.connectedSpace_of_subsingleton PA.abelian.scheme.hom
  apply AbelianScheme.FrobeniusKernel.FiniteCancellation.Construction.cancel_finite_group_map (AbelianScheme.FrobeniusKernel.PicardPullback.Construction.IntrinsicPicardPullback.dualMap f.hom PA.dual PB.dual)
  rw [Category.assoc, ← AbelianScheme.FrobeniusKernel.PicardPullback.Construction.IntrinsicPicardPullback.dualMap_comp]
  simp only [isogenyComplement_projection]
  rw [polarization_scalar_dual PA ρ hρ]
  simpa only [AbelianScheme.FrobeniusKernel.PolarizationComparison.Construction.polarizationPullbackHom, Category.assoc] using hpol.symm

end

end OAI.AlgebraicGeometry.Isogenies.NeighborCounting.IsogenyComplement

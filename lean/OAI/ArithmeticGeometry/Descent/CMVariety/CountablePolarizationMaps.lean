import OAI.ArithmeticGeometry.Descent.CMVariety.CountableGroupMaps
import OAI.ArithmeticGeometry.Descent.CMVariety.StandardModuli
import OAI.AlgebraicGeometry.AbelianScheme.CentralAction.PolarizationEtale
import OAI.AlgebraicGeometry.PELModuli.IntegralModel.IsogenyComplementGeometry
import OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.FiniteCancellation
import OAI.AlgebraicGeometry.AbelianScheme.HomExtensionLocalRings

/-! # Countable Polarization Maps -/

namespace OAI.ArithmeticGeometry.Descent.CMVariety.CountablePolarizationMaps.Abelian

noncomputable section

/-!
Group maps from a presented complex abelian scheme to its actual dual
form a countable set. A complementary polarization isogeny embeds them
into its endomorphisms, using finite-kernel cancellation on the connected
reduced source. The dual needs no separate projective presentation.
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj

theorem presented_endomorphisms_countable {g : ℕ}
    (A : AlgebraicGeometry.AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase) (P : StandardModuli.Abelian.ComplexAbelianPresentation A) :
    Countable {f : A.scheme ⟶ A.scheme // IsMonHom f} := by
  let : Countable {f : P.variety.toOver ⟶ P.variety.toOver // IsMonHom f} :=
    CountableGroupMaps.Abelian.IntrinsicPeriods.algebraic_group_maps_countable P.variety P.variety
  let enc (f : {f : A.scheme ⟶ A.scheme // IsMonHom f}) :
      {f : P.variety.toOver ⟶ P.variety.toOver // IsMonHom f} := by
    let : IsMonHom f.val := f.property
    exact ⟨P.comparison.inv ≫ f.val ≫ P.comparison.hom, inferInstance⟩
  apply Function.Injective.countable (f := enc)
  intro a b hab
  apply Subtype.ext
  have h := congrArg Subtype.val hab
  change P.comparison.inv ≫ a.val ≫ P.comparison.hom =
    P.comparison.inv ≫ b.val ≫ P.comparison.hom at h
  exact (cancel_mono P.comparison.hom).mp ((cancel_epi P.comparison.inv).mp h)

theorem dual_group_maps_countable {g N : ℕ} {δ : Fin g → ℕ}
    (A : AlgebraicGeometry.AbelianModuli.HilbertConstruction.PolarizationData.PolarizedAbelianWithFullLevel g δ N AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase)
    (P : StandardModuli.Abelian.ComplexAbelianPresentation A.abelian) :
    Countable {f : A.abelian.scheme ⟶ A.dual.abelian.scheme // IsMonHom f} := by
  let : Etale A.polarization.isogeny.hom.left :=
    AlgebraicGeometry.AbelianScheme.CentralAction.PolarizationEtale.Construction.polarization_etale A.polarization.isogeny δ A.polarization.kernelType
  obtain ⟨_, q, _, hq, hfin, _, _, _, _, _⟩ :=
    AlgebraicGeometry.PELModuli.IntegralModel.IsogenyComplementGeometry.exists_complementary_finite_etale_isogeny A.polarization.isogeny.hom
  let : IsMonHom q := hq
  let : IsFinite q.left := hfin
  let : IsIntegral A.abelian.scheme.left :=
    AlgebraicGeometry.AbelianScheme.HomExtensionLocalRings.LocalRings.integral_of_smooth_proper_connected A.abelian.scheme.hom
  let : Countable {f : A.abelian.scheme ⟶ A.abelian.scheme // IsMonHom f} :=
    presented_endomorphisms_countable A.abelian P
  let enc (f : {f : A.abelian.scheme ⟶ A.dual.abelian.scheme // IsMonHom f}) :
      {f : A.abelian.scheme ⟶ A.abelian.scheme // IsMonHom f} := by
    let : IsMonHom f.val := f.property
    exact ⟨f.val ≫ q, inferInstance⟩
  apply Function.Injective.countable (f := enc)
  intro a b hab
  let : IsMonHom a.val := a.property
  let : IsMonHom b.val := b.property
  exact Subtype.ext (AlgebraicGeometry.AbelianScheme.FrobeniusKernel.FiniteCancellation.Construction.cancel_finite_group_map q a.val b.val
    (congrArg Subtype.val hab))

end

end OAI.ArithmeticGeometry.Descent.CMVariety.CountablePolarizationMaps.Abelian

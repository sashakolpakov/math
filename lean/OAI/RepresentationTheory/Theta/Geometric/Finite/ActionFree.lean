import OAI.RepresentationTheory.Theta.Geometric.Reference.ModuliOrbits
import OAI.AlgebraicGeometry.AbelianScheme.TateComparison.ComplexPELRigidity

/-! # Action Free -/

namespace OAI.RepresentationTheory.Theta.Geometric

noncomputable section

/-! The exact finite arithmetic subgroup acts freely on the original
ball at level at least three, by actual polarized full-level rigidity. -/

set_option backward.isDefEq.respectTransparency false
open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj

open OAI.AlgebraicGeometry.AbelianScheme.TateComparison.ComplexPELRigidity

variable {E K : Type} [Field E] [NumberField E] [NumberField.IsCMField E]
    [Field K] [NumberField K] {s q : ℕ} [Fact q.Prime]
    {Index Ga MpR MpF MpA : Type} [Fintype Index] [DecidableEq Index]
    [Group Ga] [TopologicalSpace Ga] [Group MpR] [Group MpF] [Group MpA]
    (D : Data.ActiveHeckeThetaData E K s q Index Ga MpR MpF MpA)

theorem Data.ActiveHeckeThetaData.rationalLinear_injective : Function.Injective D.rationalLinear :=
  Matrix.SpecialLinearGroup.toLin'_injective.comp Subtype.val_injective

variable (hg : D.pel.HasIntegralModelGeometry) (hc : D.HasFiniteCoordinates)
    (hgood : D.pel.IsGoodCompletelySplitPrime) (hdegree : Module.finrank ℚ E = 2 * s)

include hg hc hgood hdegree in
theorem Data.ActiveHeckeThetaData.finiteIntegral_fixedPoint (g : D.RationalSU)
    (hf : D.rationalFinite g ∈ (SphericalGU.Spherical.integralSL3 q).prod D.awayLevel.toSubgroup)
    (x : D.domain) (hx : D.periodMap g x.val = x.val) : g = 1 := by
  let R := D.referencePELPointData hg x
  let : IsIntegral R.model.abelian.toOver.left := R.model.abelian.variety.property
  have hΛ := D.finiteIntegral_preserves_reference_lattice hg hc hgood hdegree g hf
  obtain ⟨e, he⟩ := Data.ActiveHeckeThetaData.integralRational_markedFamilyIso_to g hΛ hgood hc hf.2 x R R (Subtype.ext hx.symm)
  let : IsMonHom (e.abelian.hom : R.model.abelian.toOver ⟶ R.model.abelian.toOver) := e.abelianGroup
  have hid := e.complex_abelian_eq_id R.family_isPEL.1 hg.fullLevel
  have hl := (AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.IntegralMaps.IntrinsicLinearMaps.rationalLift_congr (A := R.model.abelian) (B := R.model.abelian)
    e.abelian.hom (𝟙 R.model.abelian.toOver) hid).trans
    (AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.IntegralMaps.IntrinsicLinearMaps.rationalLift_id R.model.abelian)
  apply D.rationalLinear_injective
  rw [map_one]
  apply LinearEquiv.ext
  intro v
  apply (R.model.toNativeReferenceModel R.analytic).nativeReferenceMarking.injective
  exact (he v).symm.trans (LinearMap.congr_fun hl _)

end

end OAI.RepresentationTheory.Theta.Geometric

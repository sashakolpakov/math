import OAI.NumberTheory.PadicHodge.IntegralComparison.Projective.FormQuasicoherence
import OAI.NumberTheory.PadicHodge.IntegralComparison.AffineSection.Detection
import OAI.AlgebraicGeometry.SheafCohomology.Projective.RankOneMapCoordinates
import OAI.AlgebraicGeometry.SheafCohomology.Projective.InvertibleFinitePresentation

/-! # Top Form Iso -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Projective.TopFormIso

noncomputable section

/-! The canonical top differential sheaf of actual projective space is
the actual hyperplane-ideal power O(-n-1), with normalized chart frames. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry Opposite _root_.MvPolynomial

open OAI.NumberTheory.PadicHodge.IntegralComparison.Projective.IntrinsicOverlap.Intrinsic OAI.NumberTheory.PadicHodge.IntegralComparison.Projective.TopFormMap
  FormSectionIso

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

universe u
variable {R : Type u} [CommRing R] {n : ℕ}
attribute [local instance] MvPolynomial.gradedAlgebra

local instance sectionAlgebra (U : (IntrinsicOverlap.Intrinsic.space R n).Opens) : Algebra R Γ(IntrinsicOverlap.Intrinsic.space R n, U) :=
  ChartAlgebra.algebra U

def topSectionCoordinate (i : Fin (n + 1)) :
    Γ(TopFormMap.forms R n, AlgebraicGeometry.SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.coordinateOpen (R := R) i) ≃ₗ[Γ(IntrinsicOverlap.Intrinsic.space R n, AlgebraicGeometry.SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.coordinateOpen i)]
      Γ(IntrinsicOverlap.Intrinsic.space R n, AlgebraicGeometry.SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.coordinateOpen i) :=
  (show Γ(TopFormMap.forms R n, AlgebraicGeometry.SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.coordinateOpen (R := R) i) ≃ₗ[Γ(IntrinsicOverlap.Intrinsic.space R n, AlgebraicGeometry.SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.coordinateOpen i)]
      AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.Form R (IntrinsicOverlap.Intrinsic.ring R n (AlgebraicGeometry.SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.coordinateOpen i)) n from
    (FormSectionIso.sectionUnitIso (R := R) i n).symm).trans
      (show AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.Form R (IntrinsicOverlap.Intrinsic.ring R n (AlgebraicGeometry.SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.coordinateOpen i)) n ≃ₗ[Γ(IntrinsicOverlap.Intrinsic.space R n, AlgebraicGeometry.SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.coordinateOpen i)]
        Γ(IntrinsicOverlap.Intrinsic.space R n, AlgebraicGeometry.SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.coordinateOpen i) from IntrinsicTopForms.Intrinsic.topEquiv i)

theorem topSectionCoordinate_generator (i : Fin (n + 1)) :
    topSectionCoordinate (R := R) i (TopFormMap.coordinateSection R n i) = (-1) ^ i.val := by
  change IntrinsicTopForms.Intrinsic.topEquiv i
    ((FormSectionIso.sectionUnitIso (R := R) i n).symm
      ((FormSectionIso.sectionUnitIso (R := R) i n) (IntrinsicOverlap.Intrinsic.generator i))) = _
  rw [LinearEquiv.symm_apply_apply]
  have hg : IntrinsicOverlap.Intrinsic.generator (R := R) i = (-1 : Γ(IntrinsicOverlap.Intrinsic.space R n, AlgebraicGeometry.SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.coordinateOpen i)) ^ i.val •
      IntrinsicTopForms.Intrinsic.generator (R := R) i :=
    AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.symbol_smul_one R (IntrinsicOverlap.Intrinsic.ring R n (AlgebraicGeometry.SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.coordinateOpen i)) _ _
  rw [hg, map_smul, IntrinsicTopForms.Intrinsic.topEquiv_generator, smul_eq_mul, mul_one]

theorem map_chart_bijective (j i : Fin (n + 1)) :
    Function.Bijective ((TopFormMap.map R n j).val.app (op (AlgebraicGeometry.SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.coordinateOpen i))) := by
  let S := Γ(IntrinsicOverlap.Intrinsic.space R n, AlgebraicGeometry.SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.coordinateOpen (R := R) i)
  let N := AlgebraicGeometry.SheafCohomology.Projective.TwistPowers.MvPolynomial.coordinateHyperplaneIdealModulePower (R := R) j (n + 1)
  let eM := AlgebraicGeometry.SheafCohomology.Projective.RankOneMapCoordinates.overFrameSectionEquiv N (AlgebraicGeometry.SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.coordinateOpen i)
    (AlgebraicGeometry.SheafCohomology.Projective.NegativeTwistMaps.MvPolynomial.coordinateHyperplaneIdealModulePowerOverFrame i j (n + 1))
  let eN := topSectionCoordinate (R := R) i
  let f := (TopFormMap.map R n j).val.app (op (AlgebraicGeometry.SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.coordinateOpen i))
  let c : Sˣ := (-1) ^ i.val
  let eC : S ≃ₗ[S] S := LinearEquiv.smulOfUnit c
  have hframe : f (eM 1) = TopFormMap.coordinateSection R n i := TopFormMap.map_frame R n j i
  have hcoord (r : S) : eN (f (eM r)) = eC r := by
    have hr : eM r = r • eM 1 := by rw [← map_smul, smul_eq_mul, mul_one]
    rw [hr, map_smul, hframe, map_smul]
    change r * topSectionCoordinate (R := R) i (TopFormMap.coordinateSection R n i) = eC r
    rw [topSectionCoordinate_generator]
    change r * (-1) ^ i.val = ((-1 : Sˣ) ^ i.val : Sˣ) • r
    simp only [Units.smul_def, Units.val_pow_eq_pow_val, Units.val_neg, Units.val_one, smul_eq_mul]
    exact mul_comm _ _
  constructor
  · intro a b hab
    obtain ⟨a, rfl⟩ := eM.surjective a
    obtain ⟨b, rfl⟩ := eM.surjective b
    apply congrArg eM
    apply eC.injective
    rw [← hcoord, ← hcoord, hab]
  · intro z
    refine ⟨eM (eC.symm (eN z)), ?_⟩
    apply eN.injective
    rw [hcoord, LinearEquiv.apply_symm_apply]

theorem map_isIso (j : Fin (n + 1)) : IsIso (TopFormMap.map R n j) := by
  let N := AlgebraicGeometry.SheafCohomology.Projective.TwistPowers.MvPolynomial.coordinateHyperplaneIdealModulePower (R := R) j (n + 1)
  let : N.IsQuasicoherent := AlgebraicGeometry.SheafCohomology.Projective.InvertibleFinitePresentation.invertible_quasicoherent
    (AlgebraicGeometry.SheafCohomology.Projective.TwistPowers.MvPolynomial.coordinateHyperplaneIdealModulePower_isInvertible j (n + 1))
  let : (TopFormMap.forms R n).IsQuasicoherent := FormQuasicoherence.quasicoherent (R := R) n
  apply AffineSection.Detection.cover (TopFormMap.map R n j)
    (fun i : ULift.{u} (Fin (n + 1)) => AlgebraicGeometry.SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.coordinateOpen i.down)
  · simpa only [iSup_ulift] using (AlgebraicGeometry.SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.iSup_coordinateOpen_eq_top (R := R) (σ := Fin (n + 1)))
  · intro i
    exact AlgebraicGeometry.SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.coordinateOpen_isAffineOpen i.down
  · intro i
    apply (ConcreteCategory.isIso_iff_bijective _).mpr
    exact map_chart_bijective j i.down

def iso (j : Fin (n + 1)) :
    AlgebraicGeometry.SheafCohomology.Projective.TwistPowers.MvPolynomial.coordinateHyperplaneIdealModulePower (R := R) j (n + 1) ≅ TopFormMap.forms R n := by
  letI := map_isIso (R := R) j
  exact asIso (TopFormMap.map R n j)

theorem iso_frame (j i : Fin (n + 1)) :
    (iso (R := R) j).hom.val.app (op (AlgebraicGeometry.SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.coordinateOpen i))
      (AlgebraicGeometry.SheafCohomology.Projective.NegativeTwistMaps.MvPolynomial.coordinateHyperplaneIdealModulePowerFrameSection (R := R) i j (n + 1)) = TopFormMap.coordinateSection R n i :=
  TopFormMap.map_frame R n j i

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Projective.TopFormIso

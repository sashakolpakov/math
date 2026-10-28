import OAI.NumberTheory.PadicHodge.IntegralComparison.Projective.IntrinsicOverlap
import OAI.NumberTheory.PadicHodge.IntegralComparison.Integral.FormSectionUnit

/-! # Top Form Map -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Projective.TopFormMap

noncomputable section

/-! Gluing the exact signed coordinate differentials gives a morphism from
the genuine negative canonical twist to the original top-form sheaf. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry Opposite _root_.MvPolynomial

open OAI.NumberTheory.PadicHodge.IntegralComparison.Projective.IntrinsicOverlap.Intrinsic

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

universe u
variable (R : Type u) [CommRing R] (n : ℕ)
attribute [local instance] MvPolynomial.gradedAlgebra

abbrev forms : (IntrinsicOverlap.Intrinsic.space R n).Modules := GeometricComparison.Integral.FormsModules.IntegralFormsModules.sheaf R (IntrinsicOverlap.Intrinsic.model R n) n

local instance sectionModule (U : (IntrinsicOverlap.Intrinsic.space R n).Opens) :
    Module (IntrinsicOverlap.Intrinsic.ring R n U) Γ(forms R n, U) :=
  inferInstanceAs (Module Γ(IntrinsicOverlap.Intrinsic.space R n, U) Γ(forms R n, U))

def coordinateSection (i : Fin (n + 1)) : Γ(forms R n, AlgebraicGeometry.SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.coordinateOpen (R := R) i) :=
  Integral.FormSectionUnit.unit R (IntrinsicOverlap.Intrinsic.model R n) n (AlgebraicGeometry.SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.coordinateOpen i) (IntrinsicOverlap.Intrinsic.generator i)

theorem section_transition (i k : Fin (n + 1)) :
    (forms R n).presheaf.map (homOfLE (AlgebraicGeometry.SheafCohomology.Projective.CoordinateExtensions.MvPolynomial.coordinateOpenOverlap_le_left (R := R) i k)).op (coordinateSection R n i) =
      (AlgebraicGeometry.SheafCohomology.Projective.CoordinateExtensions.MvPolynomial.coordinateOpenTransitionUnit (R := R) i k :
        Γ(IntrinsicOverlap.Intrinsic.space R n, AlgebraicGeometry.SheafCohomology.Projective.CoordinateExtensions.MvPolynomial.coordinateOpenOverlap (R := R) i k)) ^ (n + 1) •
      (forms R n).presheaf.map (homOfLE (AlgebraicGeometry.SheafCohomology.Projective.CoordinateExtensions.MvPolynomial.coordinateOpenOverlap_le_right (R := R) i k)).op (coordinateSection R n k) := by
  rw [coordinateSection, coordinateSection, Integral.FormSectionUnit.restriction,
    Integral.FormSectionUnit.restriction]
  rw [IntrinsicOverlap.Intrinsic.generator_transition]
  exact (Integral.FormSectionUnit.unit R (IntrinsicOverlap.Intrinsic.model R n) n (AlgebraicGeometry.SheafCohomology.Projective.CoordinateExtensions.MvPolynomial.coordinateOpenOverlap i k)).map_smul
    ((AlgebraicGeometry.SheafCohomology.Projective.CoordinateExtensions.MvPolynomial.coordinateOpenTransitionUnit (R := R) i k : Γ(IntrinsicOverlap.Intrinsic.space R n, AlgebraicGeometry.SheafCohomology.Projective.CoordinateExtensions.MvPolynomial.coordinateOpenOverlap i k)) ^ (n + 1)) _

theorem exists_map (j : Fin (n + 1)) :
    ∃ f : AlgebraicGeometry.SheafCohomology.Projective.TwistPowers.MvPolynomial.coordinateHyperplaneIdealModulePower (R := R) j (n + 1) ⟶ forms R n,
      ∀ i, f.val.app (op (AlgebraicGeometry.SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.coordinateOpen (R := R) i))
        (AlgebraicGeometry.SheafCohomology.Projective.NegativeTwistMaps.MvPolynomial.coordinateHyperplaneIdealModulePowerFrameSection (R := R) i j (n + 1)) = coordinateSection R n i :=
  AlgebraicGeometry.SheafCohomology.Projective.NegativeTwistMaps.MvPolynomial.exists_coordinateNegativeTwistHom_of_coefficients (forms R n) j (n + 1)
    (coordinateSection R n) (section_transition R n)

def map (j : Fin (n + 1)) :
    AlgebraicGeometry.SheafCohomology.Projective.TwistPowers.MvPolynomial.coordinateHyperplaneIdealModulePower (R := R) j (n + 1) ⟶ forms R n :=
  (exists_map R n j).choose

theorem map_frame (j i : Fin (n + 1)) :
    (TopFormMap.map R n j).val.app (op (AlgebraicGeometry.SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.coordinateOpen (R := R) i))
      (AlgebraicGeometry.SheafCohomology.Projective.NegativeTwistMaps.MvPolynomial.coordinateHyperplaneIdealModulePowerFrameSection (R := R) i j (n + 1)) = coordinateSection R n i :=
  (exists_map R n j).choose_spec i

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Projective.TopFormMap

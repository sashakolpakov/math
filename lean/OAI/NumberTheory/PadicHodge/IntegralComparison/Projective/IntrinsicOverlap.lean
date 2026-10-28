import OAI.NumberTheory.PadicHodge.IntegralComparison.Projective.IntrinsicTopForms
import OAI.NumberTheory.PadicHodge.IntegralComparison.Projective.OrientedDifferentials
import OAI.NumberTheory.PadicHodge.IntegralComparison.AffineOpen.DifferentialBasis
import OAI.AlgebraicGeometry.SheafCohomology.Projective.NegativeTwistMaps

/-! # Intrinsic Overlap -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Projective.IntrinsicOverlap.Intrinsic

noncomputable section

/-! The original differential-symbol top forms on projective charts have
the actual hyperplane-ideal transition on their genuine affine overlaps. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry Opposite _root_.MvPolynomial

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

universe u
variable (R : Type u) [CommRing R] (n : ℕ)
attribute [local instance] MvPolynomial.gradedAlgebra

abbrev space := Proj (homogeneousSubmodule (Fin (n + 1)) R)
abbrev model : Over (Spec (CommRingCat.of R)) :=
  Over.mk (AlgebraicGeometry.SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.homogeneousProjπ (R := R) (σ := Fin (n + 1)))
abbrev ring (U : (space R n).Opens) := IntrinsicDeRham.SectionUnit.Intrinsic.ring R (model R n) U

variable {R n}

theorem overlap_affine (i k : Fin (n + 1)) :
    IsAffineOpen (AlgebraicGeometry.SheafCohomology.Projective.CoordinateExtensions.MvPolynomial.coordinateOpenOverlap (R := R) i k) := by
  rw [← AlgebraicGeometry.SheafCohomology.Projective.CoordinateExtensions.MvPolynomial.coordinateHyperplaneLocalEquation_basicOpen]
  exact (AlgebraicGeometry.SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.coordinateOpen_isAffineOpen i).basicOpen _

def restrictedBasis (i : Fin (n + 1)) {V : (space R n).Opens}
    (a : V ⟶ AlgebraicGeometry.SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.coordinateOpen (R := R) i) (hV : IsAffineOpen V) :
    Module.Basis (ULift.{u} (Fin n)) (ring R n V) Ω[ring R n V⁄R] :=
  AffineOpen.DifferentialBasis.basis R (model R n) a
    (AlgebraicGeometry.SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.coordinateOpen_isAffineOpen i) hV (IntrinsicTopForms.Intrinsic.liftedBasis i)

def restrictedCoordinate (i : Fin (n + 1)) {V : (space R n).Opens}
    (a : V ⟶ AlgebraicGeometry.SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.coordinateOpen (R := R) i) (j : ULift.{u} (Fin n)) : ring R n V :=
  ((AlgebraicGeometry.Crystalline.Cohomology.AlgebraicForms.AlgebraicDeRham.sectionAlgebras R (model R n)).map a.op).hom
    (AlgebraicGeometry.SheafCohomology.Projective.CoordinateExtensions.MvPolynomial.coordinateHyperplaneLocalEquation (R := R) i (i.succAbove j.down))

theorem restrictedBasis_apply (i : Fin (n + 1)) {V : (space R n).Opens}
    (a : V ⟶ AlgebraicGeometry.SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.coordinateOpen (R := R) i) (hV : IsAffineOpen V) (j : ULift.{u} (Fin n)) :
    restrictedBasis i a hV j = KaehlerDifferential.D R (ring R n V) (restrictedCoordinate i a j) :=
  AffineOpen.DifferentialBasis.basis_apply R (model R n) a
    (AlgebraicGeometry.SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.coordinateOpen_isAffineOpen i) hV (IntrinsicTopForms.Intrinsic.liftedBasis i)
    (IntrinsicTopForms.Intrinsic.coordinate i) (IntrinsicTopForms.Intrinsic.liftedBasis_apply i) j

def restrictedExteriorEquiv (i : Fin (n + 1)) {V : (space R n).Opens}
    (a : V ⟶ AlgebraicGeometry.SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.coordinateOpen (R := R) i) (hV : IsAffineOpen V) (d : ℕ) :
    AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.Form R (ring R n V) d ≃ₗ[ring R n V] ⋀[ring R n V]^d Ω[ring R n V⁄R] :=
  ExactDifferentialBasis.exteriorEquiv R (ring R n V) (ULift.{u} (Fin n))
    (restrictedCoordinate i a) d (restrictedBasis i a hV) (restrictedBasis_apply i a hV)

theorem restrictedExteriorEquiv_eq (i : Fin (n + 1)) {V : (space R n).Opens}
    (a : V ⟶ AlgebraicGeometry.SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.coordinateOpen (R := R) i) (hV : IsAffineOpen V) (d : ℕ) :
    (restrictedExteriorEquiv i a hV d).toLinearMap = AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.toExterior R (ring R n V) d :=
  ExactDifferentialBasis.exteriorEquiv_eq R (ring R n V) (ULift.{u} (Fin n))
    (restrictedCoordinate i a) d (restrictedBasis i a hV) (restrictedBasis_apply i a hV)

def generator (i : Fin (n + 1)) : AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.Form R (ring R n (AlgebraicGeometry.SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.coordinateOpen i)) n :=
  AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.symbol R (ring R n (AlgebraicGeometry.SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.coordinateOpen i)) ((-1) ^ i.val)
    (fun j => AlgebraicGeometry.SheafCohomology.Projective.CoordinateExtensions.MvPolynomial.coordinateHyperplaneLocalEquation (R := R) i (i.succAbove j))

theorem generator_transition {R : Type u} [CommRing R] {n : ℕ} (i k : Fin (n + 1)) :
    AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.formMap ((AlgebraicGeometry.Crystalline.Cohomology.AlgebraicForms.AlgebraicDeRham.sectionAlgebras R (model R n)).map
      (homOfLE (AlgebraicGeometry.SheafCohomology.Projective.CoordinateExtensions.MvPolynomial.coordinateOpenOverlap_le_left (R := R) i k)).op) n (generator i) =
    (show ring R n (AlgebraicGeometry.SheafCohomology.Projective.CoordinateExtensions.MvPolynomial.coordinateOpenOverlap i k) from (AlgebraicGeometry.SheafCohomology.Projective.CoordinateExtensions.MvPolynomial.coordinateOpenTransitionUnit (R := R) i k).val) ^ (n + 1) •
      AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.formMap ((AlgebraicGeometry.Crystalline.Cohomology.AlgebraicForms.AlgebraicDeRham.sectionAlgebras R (model R n)).map
        (homOfLE (AlgebraicGeometry.SheafCohomology.Projective.CoordinateExtensions.MvPolynomial.coordinateOpenOverlap_le_right (R := R) i k)).op) n (generator k) := by
  let V := AlgebraicGeometry.SheafCohomology.Projective.CoordinateExtensions.MvPolynomial.coordinateOpenOverlap (R := R) i k
  let a : V ⟶ AlgebraicGeometry.SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.coordinateOpen (R := R) i := homOfLE (AlgebraicGeometry.SheafCohomology.Projective.CoordinateExtensions.MvPolynomial.coordinateOpenOverlap_le_left i k)
  let b : V ⟶ AlgebraicGeometry.SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.coordinateOpen (R := R) k := homOfLE (AlgebraicGeometry.SheafCohomology.Projective.CoordinateExtensions.MvPolynomial.coordinateOpenOverlap_le_right i k)
  let u : (ring R n V)ˣ := AlgebraicGeometry.SheafCohomology.Projective.CoordinateExtensions.MvPolynomial.coordinateOpenTransitionUnit i k
  let x : Fin (n + 1) → ring R n V := fun j =>
    ((AlgebraicGeometry.Crystalline.Cohomology.AlgebraicForms.AlgebraicDeRham.sectionAlgebras R (model R n)).map a.op).hom
      (AlgebraicGeometry.SheafCohomology.Projective.CoordinateExtensions.MvPolynomial.coordinateHyperplaneLocalEquation i j)
  let y : Fin (n + 1) → ring R n V := fun j =>
    ((AlgebraicGeometry.Crystalline.Cohomology.AlgebraicForms.AlgebraicDeRham.sectionAlgebras R (model R n)).map b.op).hom
      (AlgebraicGeometry.SheafCohomology.Projective.CoordinateExtensions.MvPolynomial.coordinateHyperplaneLocalEquation k j)
  have hi : x i = 1 := by
    dsimp only [x]
    rw [AlgebraicGeometry.SheafCohomology.Projective.CoordinateExtensions.MvPolynomial.coordinateHyperplaneLocalEquation_self]
    exact map_one _
  have hk : x k = (u : ring R n V) := rfl
  have hy (j : Fin (n + 1)) : ((u⁻¹ : (ring R n V)ˣ) : ring R n V) * x j = y j := by
    have hxy : x j = (u : ring R n V) * y j :=
      AlgebraicGeometry.SheafCohomology.Projective.CoordinateExtensions.MvPolynomial.coordinateHyperplaneLocalEquation_restrict_eq_transition_mul i k j
    rw [hxy, ← mul_assoc, Units.inv_mul, one_mul]
  apply (restrictedExteriorEquiv i a (overlap_affine i k) n).injective
  change (restrictedExteriorEquiv i a (overlap_affine i k) n).toLinearMap _ =
    (restrictedExteriorEquiv i a (overlap_affine i k) n).toLinearMap _
  rw [restrictedExteriorEquiv_eq]
  simp only [generator, AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.formMap_symbol, map_pow, map_neg, map_one,
    map_smul]
  change AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.toExterior R (ring R n V) n
      (AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.symbol R (ring R n V) ((-1) ^ i.val) (fun j => x (i.succAbove j))) =
    (u : ring R n V) ^ (n + 1) • AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.toExterior R (ring R n V) n
      (AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.symbol R (ring R n V) ((-1) ^ k.val) (fun j => y (k.succAbove j)))
  rw [AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.toExterior_symbol, AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.toExterior_symbol]
  change (-1 : ring R n V) ^ i.val •
      exteriorPower.ιMulti (ring R n V) n (fun j => KaehlerDifferential.D R (ring R n V) (x (i.succAbove j))) =
    (u : ring R n V) ^ (n + 1) • ((-1 : ring R n V) ^ k.val •
      exteriorPower.ιMulti (ring R n V) n (fun j => KaehlerDifferential.D R (ring R n V) (y (k.succAbove j))))
  by_cases hik : k = i
  · subst k
    have hu : (u : ring R n V) = 1 := hk.symm.trans hi
    have hxy : x = y := by
      funext j
      have h := hy j
      have hui : ((u⁻¹ : (ring R n V)ˣ) : ring R n V) = 1 := by
        rw [show u = 1 from Units.ext hu]
        rfl
      simpa only [hui, one_mul] using h
    rw [hu, one_pow, one_smul, hxy]
  · have h := OrientedDifferentials.oriented_wedge_transition
      (KaehlerDifferential.D R (ring R n V)) i k hik u x hi hk
    simpa only [hy] using h

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Projective.IntrinsicOverlap.Intrinsic

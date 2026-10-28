import OAI.NumberTheory.PadicHodge.IntegralComparison.DifferentialBasisLocalization
import OAI.NumberTheory.PadicHodge.IntegralComparison.Projective.AmbientAdjunction
import OAI.NumberTheory.PadicHodge.IntegralComparison.ParameterLineAdjunction
import OAI.NumberTheory.PadicHodge.IntegralComparison.AffinePrincipal.Sections

/-! # Parameter Neighborhood -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Projective.ParameterNeighborhood

noncomputable section

/-! The actual principal open on which prescribed normal equations and
lifted parameters form the differential basis of the ambient projective
chart. Its top wedge defines a frame of the original dualizing line. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry Opposite _root_.MvPolynomial _root_.Module

open OAI.NumberTheory.PadicHodge.IntegralComparison.Projective.IntrinsicOverlap.Intrinsic

universe u
variable {R : Type u} [CommRing R] {c g : ℕ}
attribute [local instance] MvPolynomial.gradedAlgebra

local instance sectionAlgebra (U : (IntrinsicOverlap.Intrinsic.space R (c + g)).Opens) :
    Algebra R Γ(IntrinsicOverlap.Intrinsic.space R (c + g), U) :=
  AlgebraicGeometry.Crystalline.Cohomology.AlgebraicForms.AlgebraicDeRham.sectionAlgebra R (IntrinsicOverlap.Intrinsic.model R (c + g)) U

variable (i : Fin (c + g + 1)) (U : (IntrinsicOverlap.Intrinsic.space R (c + g)).Opens)
  (hU : IsAffineOpen U) (hUi : U ≤ AlgebraicGeometry.SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.coordinateOpen (R := R) i)
  (s : Fin c → Γ(IntrinsicOverlap.Intrinsic.space R (c + g), U)) (t : Fin g → Γ(IntrinsicOverlap.Intrinsic.space R (c + g), U))

abbrev determinant : Γ(IntrinsicOverlap.Intrinsic.space R (c + g), U) :=
  DifferentialBasisNeighborhood.determinant
    (AmbientAdjunction.differentialBasis i U hU hUi) (Fin.append s t)

abbrev openSubset : (IntrinsicOverlap.Intrinsic.space R (c + g)).Opens :=
  (IntrinsicOverlap.Intrinsic.space R (c + g)).basicOpen (determinant i U hU hUi s t)

theorem affine : IsAffineOpen (openSubset i U hU hUi s t) :=
  hU.basicOpen (determinant i U hU hUi s t)

theorem below : openSubset i U hU hUi s t ≤ U :=
  (IntrinsicOverlap.Intrinsic.space R (c + g)).basicOpen_le (determinant i U hU hUi s t)

theorem below_chart : openSubset i U hU hUi s t ≤ AlgebraicGeometry.SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.coordinateOpen (R := R) i :=
  (below i U hU hUi s t).trans hUi

local instance principalBaseTower :
    IsScalarTower R Γ(IntrinsicOverlap.Intrinsic.space R (c + g), U)
      Γ(IntrinsicOverlap.Intrinsic.space R (c + g), openSubset i U hU hUi s t) :=
  IsScalarTower.of_algebraMap_eq (fun a =>
    (((AlgebraicGeometry.Crystalline.Cohomology.AlgebraicForms.AlgebraicDeRham.sectionAlgebras R (IntrinsicOverlap.Intrinsic.model R (c + g))).map
      (homOfLE (below i U hU hUi s t)).op).hom.commutes a).symm)

local instance localization : IsLocalization.Away (determinant i U hU hUi s t)
    Γ(IntrinsicOverlap.Intrinsic.space R (c + g), openSubset i U hU hUi s t) :=
  hU.isLocalization_basicOpen (determinant i U hU hUi s t)

def normal : Fin c → Γ(IntrinsicOverlap.Intrinsic.space R (c + g), openSubset i U hU hUi s t) :=
  fun j => algebraMap Γ(IntrinsicOverlap.Intrinsic.space R (c + g), U)
    Γ(IntrinsicOverlap.Intrinsic.space R (c + g), openSubset i U hU hUi s t) (s j)

def parameter : Fin g → Γ(IntrinsicOverlap.Intrinsic.space R (c + g), openSubset i U hU hUi s t) :=
  fun j => algebraMap Γ(IntrinsicOverlap.Intrinsic.space R (c + g), U)
    Γ(IntrinsicOverlap.Intrinsic.space R (c + g), openSubset i U hU hUi s t) (t j)

def basis : Basis (Fin (c + g)) Γ(IntrinsicOverlap.Intrinsic.space R (c + g), openSubset i U hU hUi s t)
    Ω[Γ(IntrinsicOverlap.Intrinsic.space R (c + g), openSubset i U hU hUi s t)⁄R] :=
  DifferentialBasisLocalization.Neighborhood.basisAt
    (AmbientAdjunction.differentialBasis i U hU hUi) (Fin.append s t)
    Γ(IntrinsicOverlap.Intrinsic.space R (c + g), openSubset i U hU hUi s t)

theorem basis_eq :
    (basis i U hU hUi s t : Fin (c + g) →
      Ω[Γ(IntrinsicOverlap.Intrinsic.space R (c + g), openSubset i U hU hUi s t)⁄R]) =
    Fin.append
      (fun j => KaehlerDifferential.D R _ (normal i U hU hUi s t j))
      (fun j => KaehlerDifferential.D R _ (parameter i U hU hUi s t j)) := by
  funext j
  rw [basis, DifferentialBasisLocalization.Neighborhood.basisAt_apply]
  refine Fin.addCases (fun q => ?_) (fun q => ?_) j <;>
    simp only [Fin.append_left, Fin.append_right, normal, parameter]

def frame (j : Fin (c + g + 1)) :
    (AffineOpen.InternalHom.sections (openSubset i U hU hUi s t)
      (affine i U hU hUi s t)).obj
      (AlgebraicGeometry.SheafCohomology.Projective.TwistPowers.MvPolynomial.coordinateHyperplaneIdealModulePower (R := R) j (c + g + 1)) ≅
    ModuleCat.of Γ(IntrinsicOverlap.Intrinsic.space R (c + g), openSubset i U hU hUi s t)
      Γ(IntrinsicOverlap.Intrinsic.space R (c + g), openSubset i U hU hUi s t) :=
  ParameterLineAdjunction.frame (basis i U hU hUi s t) _
    (AmbientAdjunction.chartLineExterior i
      (openSubset i U hU hUi s t) (affine i U hU hUi s t)
      (below_chart i U hU hUi s t) j)

abbrev frame_inv (j : Fin (c + g + 1)) :=
  ParameterLineAdjunction.frame_inv (basis i U hU hUi s t) _
    (AmbientAdjunction.chartLineExterior i
      (openSubset i U hU hUi s t) (affine i U hU hUi s t)
      (below_chart i U hU hUi s t) j)

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Projective.ParameterNeighborhood

import OAI.NumberTheory.PadicHodge.IntegralComparison.Projective.AdjunctionCharts
import OAI.NumberTheory.PadicHodge.IntegralComparison.IdealSheafPrincipalEquations
import OAI.NumberTheory.PadicHodge.IntegralComparison.Etale.SectionCoordinatesRestriction
import OAI.NumberTheory.PadicHodge.IntegralComparison.LocalizedConormalBasisTransport

/-! # Adjunction Restriction -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Projective.AdjunctionRestriction

noncomputable section

/-! Genuine projective adjunction charts are stable under principal
restriction. The restricted data use the mapped regular equations,
the localized conormal and differential bases, and the actual inherited
étale coordinates. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry Opposite _root_.MvPolynomial

open OAI.NumberTheory.PadicHodge.IntegralComparison.Projective.IntrinsicOverlap.Intrinsic
  AdjunctionCharts

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

universe u
variable {R : Type u} [CommRing R] [IsNoetherianRing R] {n : ℕ}
attribute [local instance] MvPolynomial.gradedAlgebra AdjunctionCharts.ambientAlgebra

variable (X : Over (Spec (CommRingCat.of R))) (f : X ⟶ IntrinsicOverlap.Intrinsic.model R n)
  [IsClosedImmersion f.left] (g : ℕ)
  {U : (IntrinsicOverlap.Intrinsic.space R n).Opens} {hU : IsAffineOpen U}

def data (D : AdjunctionCharts.Data X f g U hU) (r : Γ(IntrinsicOverlap.Intrinsic.space R n, U)) :
    AdjunctionCharts.Data X f g ((IntrinsicOverlap.Intrinsic.space R n).basicOpen r) (hU.basicOpen r) := by
  let V := (IntrinsicOverlap.Intrinsic.space R n).basicOpen r
  let hV : IsAffineOpen V := hU.basicOpen r
  let A := Γ(IntrinsicOverlap.Intrinsic.space R n, U)
  let B := Γ(IntrinsicOverlap.Intrinsic.space R n, V)
  let I : Ideal A := LocalAdjunction.ideal X f U hU
  let J : Ideal B := LocalAdjunction.ideal X f V hV
  let : IsLocalization.Away r B := hU.isLocalization_basicOpen r
  let : IsScalarTower R A B := IsScalarTower.of_algebraMap_eq (fun a =>
    (((AlgebraicGeometry.Crystalline.Cohomology.AlgebraicForms.AlgebraicDeRham.sectionAlgebras R (IntrinsicOverlap.Intrinsic.model R n)).map
      (homOfLE ((IntrinsicOverlap.Intrinsic.space R n).basicOpen_le r)).op).hom.commutes a).symm)
  have hJ : I.map (algebraMap A B) = J :=
    IdealSheafPrincipalEquations.ideal_map f.left.ker U hU r
  let s := IdealSheafPrincipalEquations.sequence U r D.equations
  have hs : Koszul.OrientedTopCohomology.ideal B s = J :=
    IdealSheafPrincipalEquations.generates f.left.ker U hU r D.equations D.generates
  let bI := LocalizedConormalBasisTransport.Bases.conormalBasisOfEq (A := A) (B := B) r I J hJ D.conormalBasis
  let bQ := LocalizedConormalBasisTransport.Bases.quotientBasisOfEq (A := A) (B := B) r I J hJ D.quotientBasis
  let a : (f.left ⁻¹ᵁ V) ⟶ (f.left ⁻¹ᵁ U) :=
    (TopologicalSpace.Opens.map f.left.base).map (homOfLE ((IntrinsicOverlap.Intrinsic.space R n).basicOpen_le r))
  let := D.coordinates
  let := D.coordinateTower
  let := D.coordinateEtale
  refine {
    equations := s
    generates := hs
    regular := IdealSheafPrincipalEquations.weaklyRegular U hU r D.equations D.regular
    conormalBasis := bI
    conormalBasis_apply := ?_
    quotientBasis := bQ
    coordinateIndex := D.coordinateIndex
    finiteVariables := D.finiteVariables
    coordinates := Etale.SectionCoordinatesRestriction.polynomialAlgebra R X a D.coordinateIndex
    coordinateTower := Etale.SectionCoordinatesRestriction.tower R X a D.coordinateIndex
    coordinateEtale := Etale.SectionCoordinatesRestriction.etale R X a
      (hU.preimage f.left) (hV.preimage f.left) D.coordinateIndex }
  intro j
  have hb := LocalizedConormalBasisTransport.Bases.conormalBasisOfEq_equations (A := A) (B := B) r I J hJ D.conormalBasis
    (ConormalKoszulPurity.conormalVectors A I D.equations D.generates)
    D.conormalBasis_apply j
  exact hb.trans (congrArg J.toCotangent (Subtype.ext rfl))

def chart (C : AdjunctionCharts.Chart X f g U) (r : Γ(IntrinsicOverlap.Intrinsic.space R n, U)) :
    AdjunctionCharts.Chart X f g ((IntrinsicOverlap.Intrinsic.space R n).basicOpen r) where
  affine := C.affine.basicOpen r
  coordinate := C.coordinate
  le_coordinate := ((IntrinsicOverlap.Intrinsic.space R n).basicOpen_le r).trans C.le_coordinate
  description := match C.description with
    | Sum.inl h => Sum.inl ⟨by
        have hI : f.left.ker.ideal ⟨U, C.affine⟩ = ⊤ := (f.left.ker_apply ⟨U, C.affine⟩).trans h.down
        have hJ := IdealSheafPrincipalEquations.ideal_map f.left.ker U C.affine r
        rw [hI, Ideal.map_top] at hJ
        exact (f.left.ker_apply ⟨(IntrinsicOverlap.Intrinsic.space R n).basicOpen r, C.affine.basicOpen r⟩).symm.trans hJ.symm⟩
    | Sum.inr D => Sum.inr (data X f g D r)

omit [IsNoetherianRing R] in
theorem good_principal (h : AdjunctionCharts.Good X f g U) (r : Γ(IntrinsicOverlap.Intrinsic.space R n, U)) :
    AdjunctionCharts.Good X f g ((IntrinsicOverlap.Intrinsic.space R n).basicOpen r) := by
  obtain ⟨C⟩ := h
  exact ⟨chart X f g C r⟩

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Projective.AdjunctionRestriction

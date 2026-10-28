import OAI.NumberTheory.PadicHodge.IntegralComparison.Projective.SectionClass
import OAI.NumberTheory.PadicHodge.IntegralComparison.Projective.UnitPureClass
import OAI.NumberTheory.PadicHodge.IntegralComparison.Smooth.ProjectiveFormTrace

/-! # Projective Section Class Data -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Smooth.ProjectiveSectionClassData

noncomputable section

/-! The original scalar-to-point quotient class, followed by the
original pure cohomology and top-form adjunction maps. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.MvPolynomial
open OAI.NumberTheory.PadicHodge.IntegralComparison.Projective.IntrinsicOverlap.Intrinsic OAI.NumberTheory.PadicHodge.IntegralComparison.Projective.TopTracePairing OAI.NumberTheory.PadicHodge.IntegralComparison.NegativeTwistResidueNaturality

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u
variable {R : Type u} [CommRing R] [IsNoetherianRing R] [Module.Injective R R]
  [IsArtinianRing R] [IsLocalRing R] {n : ℕ}
attribute [local instance] MvPolynomial.gradedAlgebra

variable (X : Over (Spec (CommRingCat.of R))) [Nonempty X.left]
  (i : X ⟶ Projective.IntrinsicOverlap.Intrinsic.model R (n + 1)) [IsClosedImmersion i.left]
  [Smooth X.hom] [IsProper X.hom] [GeometricallyConnected X.hom]
  (s : Spec (CommRingCat.of R) ⟶ X.left) (hs : s ≫ X.hom = 𝟙 _)
  (B : ℕ) (hB : n + 2 ≤ B) (g : ℕ) [SmoothOfRelativeDimension g X.hom]

local notation "π" => OAI.AlgebraicGeometry.SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.homogeneousProjπ (R := R) (σ := Fin (n + 2))

local instance composite_smooth : Smooth (i.left ≫ π) := by
  change Smooth (i.left ≫ (Projective.IntrinsicOverlap.Intrinsic.model R (n + 1)).hom)
  rw [Over.w i]
  infer_instance

attribute [local instance] ProjectiveFormTrace.composite_dimension
  ProjectiveFormTrace.composite_proper ProjectiveFormTrace.composite_connected

include hs in
omit [IsNoetherianRing R] [Module.Injective R R] [IsArtinianRing R] [IsLocalRing R] [Nonempty ↥X.left] [IsClosedImmersion (Over.Hom.left i)] [Smooth X.hom] [IsProper X.hom] [GeometricallyConnected X.hom] in
theorem section_over : s ≫ (i.left ≫ π) = 𝟙 _ := by
  change s ≫ (i.left ≫ (Projective.IntrinsicOverlap.Intrinsic.model R (n + 1)).hom) = 𝟙 _
  rw [Over.w i]
  exact hs

include X i in
omit [Module.Injective R R] [IsArtinianRing R] [IsLocalRing R] [Smooth X.hom] [IsProper X.hom] [GeometricallyConnected X.hom] in
theorem degree : g + (n + 1 - g) = n + 1 := by
  have h := ClosedDimension.projective i.left g
  simp only [Fintype.card_fin] at h
  omega

omit [IsNoetherianRing R] [Module.Injective R R] [Nonempty ↥X.left] [IsClosedImmersion (Over.Hom.left i)] in
theorem scalarUnit_one :
    Projective.SectionClass.scalarUnitIso i.left s (section_over X i s hs) 1 =
      Cech.StructureUnit.unit i.left π
        (AlgebraicGeometry.SheafCohomology.Projective.StandardCech.MvPolynomial.coordinateOpenCover (R := R) (σ := Fin (n + 2)))
        (AlgebraicGeometry.SheafCohomology.Projective.StandardCech.MvPolynomial.iSup_coordinateOpenCover_eq_top (R := R) (σ := Fin (n + 2))) :=
  ArtinianCechStructureUnit.iso_one i.left π s (section_over X i s hs)
    (AlgebraicGeometry.SheafCohomology.Projective.StandardCech.MvPolynomial.coordinateOpenCover (R := R) (σ := Fin (n + 2)))
    (AlgebraicGeometry.SheafCohomology.Projective.StandardCech.MvPolynomial.iSup_coordinateOpenCover_eq_top (R := R) (σ := Fin (n + 2)))

local notation "M" => OAI.NumberTheory.PadicHodge.IntegralComparison.Projective.SectionClass.scalar i.left
local notation "P" => OAI.NumberTheory.PadicHodge.IntegralComparison.Projective.SectionClass.point i.left s
local notation "hn" => Fintype.card_fin (n + 2)
local notation "hsec" => OAI.NumberTheory.PadicHodge.IntegralComparison.Smooth.ProjectiveSectionClassData.section_over X i s hs

def pureClass := by
  letI : Subsingleton (Spec (.of R)) := Ring.KrullDimLE.subsingleton_primeSpectrum R
  letI : IsClosedImmersion s := isClosedImmersion_of_comp_eq_id (i.left ≫ π) s hsec
  letI : (P).IsQuasicoherent := Finite.MapPureTrace.coefficients_quasicoherent s i.left
  letI : (P).IsFiniteType := Finite.MapPureTrace.coefficients_finiteType s i.left
  exact Projective.UnitPureClass.pureClass M P B n hn hB
    (Cech.StructurePullbackUnit.sheafMap s i.left)
    (Projective.SectionClass.scalarUnitIso i.left s hsec)
    (Projective.SectionClass.pointUnitIso i.left s hsec)
    (n + 1 - g) (ProjectiveSerre.exactAt i.left B n hn hB g) g (degree X i g)

def sectionClass : ProjectiveFormTrace.cohomology X i g :=
  (ProjectiveRefinement.Serre.cohomologyFunctor (R := R) (σ := Fin (n + 2)) g).map
    (ProjectiveFormTrace.adjunctionIso X i B hB g).hom (pureClass X i s hs B hB g)

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Smooth.ProjectiveSectionClassData

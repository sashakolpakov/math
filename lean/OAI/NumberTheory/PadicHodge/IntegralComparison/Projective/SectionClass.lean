import OAI.NumberTheory.PadicHodge.IntegralComparison.Projective.TotalUnitMap
import OAI.NumberTheory.PadicHodge.IntegralComparison.ArtinianCechStructureUnit
import OAI.NumberTheory.PadicHodge.IntegralComparison.IteratedCechStructureUnit
import OAI.NumberTheory.PadicHodge.IntegralComparison.Finite.MapPureTrace

/-! # Section Class -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Projective.SectionClass

noncomputable section

/-! The actual section quotient defines a class through the original
common negative resolution. Its projective Serre trace is one. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.MvPolynomial

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u
open OAI.NumberTheory.PadicHodge.IntegralComparison.Projective.TopTracePairing OAI.NumberTheory.PadicHodge.IntegralComparison.NegativeTwistResidueNaturality

variable {R : Type u} [CommRing R] [IsNoetherianRing R]
  [IsArtinianRing R] [IsLocalRing R] [Module.Injective R R]
  {σ : Type} [Fintype σ] [LinearOrder σ]
attribute [local instance] MvPolynomial.gradedAlgebra

variable {X : Scheme.{u}} (i : X ⟶ Proj (homogeneousSubmodule σ R)) [IsClosedImmersion i]
  [IsProper (i ≫ AlgebraicGeometry.SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.homogeneousProjπ)] [Smooth (i ≫ AlgebraicGeometry.SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.homogeneousProjπ)]
  [GeometricallyConnected (i ≫ AlgebraicGeometry.SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.homogeneousProjπ)]
  (s : Spec (.of R) ⟶ X) (hs : s ≫ (i ≫ AlgebraicGeometry.SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.homogeneousProjπ) = 𝟙 _)
  (B n : ℕ) (hn : Fintype.card σ = n + 2) (hB : n + 2 ≤ B)

abbrev scalar := Global.StructureUnit.directImage i
abbrev point := Cech.StructurePullbackUnit.coefficients s i

def scalarUnitIso := (ArtinianCechStructureUnit.iso i AlgebraicGeometry.SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.homogeneousProjπ s hs
  (AlgebraicGeometry.SheafCohomology.Projective.StandardCech.MvPolynomial.coordinateOpenCover (R := R) (σ := σ))
  (AlgebraicGeometry.SheafCohomology.Projective.StandardCech.MvPolynomial.iSup_coordinateOpenCover_eq_top (R := R) (σ := σ))).toLinearEquiv

def pointUnitIso := by
  letI : IsIso (s ≫ i ≫ AlgebraicGeometry.SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.homogeneousProjπ).appTop := by rw [hs]; infer_instance
  exact (IteratedCechStructureUnit.iso s i AlgebraicGeometry.SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.homogeneousProjπ
    (AlgebraicGeometry.SheafCohomology.Projective.StandardCech.MvPolynomial.coordinateOpenCover (R := R) (σ := σ))
    (AlgebraicGeometry.SheafCohomology.Projective.StandardCech.MvPolynomial.iSup_coordinateOpenCover_eq_top (R := R) (σ := σ))).toLinearEquiv

omit [IsNoetherianRing R] [Module.Injective R R] [Fintype σ] [IsClosedImmersion i] in
theorem unit_preserved :
    (TopCechRightExact.functor (AlgebraicGeometry.SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.homogeneousProjπ (R := R) (σ := σ))
      (AlgebraicGeometry.SheafCohomology.Projective.StandardCech.MvPolynomial.coordinateOpenCover (R := R) (σ := σ)) 0).map
      (Cech.StructurePullbackUnit.sheafMap s i) (scalarUnitIso i s hs 1) = pointUnitIso i s hs 1 := by
  let : IsIso (s ≫ i ≫ AlgebraicGeometry.SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.homogeneousProjπ).appTop := by rw [hs]; infer_instance
  change _ = (IteratedCechStructureUnit.iso s i AlgebraicGeometry.SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.homogeneousProjπ
    (AlgebraicGeometry.SheafCohomology.Projective.StandardCech.MvPolynomial.coordinateOpenCover (R := R) (σ := σ))
    (AlgebraicGeometry.SheafCohomology.Projective.StandardCech.MvPolynomial.iSup_coordinateOpenCover_eq_top (R := R) (σ := σ))).toLinearEquiv 1
  rw [IteratedCechStructureUnit.iso_one]
  rw [scalarUnitIso, ArtinianCechStructureUnit.iso_one]
  exact Cech.StructurePullbackUnit.preserves_unit s i AlgebraicGeometry.SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.homogeneousProjπ
    (AlgebraicGeometry.SheafCohomology.Projective.StandardCech.MvPolynomial.coordinateOpenCover (R := R) (σ := σ))
    (AlgebraicGeometry.SheafCohomology.Projective.StandardCech.MvPolynomial.iSup_coordinateOpenCover_eq_top (R := R) (σ := σ))

abbrev sectionClass := by
  letI : Subsingleton (Spec (.of R)) := Ring.KrullDimLE.subsingleton_primeSpectrum R
  letI : IsClosedImmersion s := isClosedImmersion_of_comp_eq_id (i ≫ AlgebraicGeometry.SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.homogeneousProjπ) s hs
  letI : (point i s).IsQuasicoherent := Finite.MapPureTrace.coefficients_quasicoherent s i
  letI : (point i s).IsFiniteType := Finite.MapPureTrace.coefficients_finiteType s i
  exact TotalUnitMap.unitClass (scalar i) (point i s) B n hn hB
    (Cech.StructurePullbackUnit.sheafMap s i) (scalarUnitIso i s hs) (pointUnitIso i s hs)

abbrev trace_one := by
  letI : Subsingleton (Spec (.of R)) := Ring.KrullDimLE.subsingleton_primeSpectrum R
  letI : IsClosedImmersion s := isClosedImmersion_of_comp_eq_id (i ≫ AlgebraicGeometry.SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.homogeneousProjπ) s hs
  letI : (point i s).IsQuasicoherent := Finite.MapPureTrace.coefficients_quasicoherent s i
  letI : (point i s).IsFiniteType := Finite.MapPureTrace.coefficients_finiteType s i
  exact TotalUnitMap.unitClass_trace (scalar i) (point i s) B n hn hB
    (Cech.StructurePullbackUnit.sheafMap s i) (scalarUnitIso i s hs) (pointUnitIso i s hs)
    (unit_preserved i s hs)

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Projective.SectionClass

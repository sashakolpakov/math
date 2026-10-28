import OAI.NumberTheory.PadicHodge.IntegralComparison.FiniteEtale.AdjunctionTrace
import OAI.NumberTheory.PadicHodge.IntegralComparison.Finite.MapCoefficientPurity
import OAI.NumberTheory.PadicHodge.IntegralComparison.Smooth.ProjectiveFormTrace

/-! # Proper Trace Base -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.FiniteEtale.ProperTraceBase

noncomputable section

/-! The proper source trace uses the target projective embedding and
actual finite coefficient algebra. The trace is the original Serre pairing evaluated at the actual unit. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.MvPolynomial
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v

open OAI.NumberTheory.PadicHodge.IntegralComparison.Projective.IntrinsicOverlap.Intrinsic OAI.NumberTheory.PadicHodge.IntegralComparison.ProjectiveCoefficient.HomLocal
open OAI.NumberTheory.PadicHodge.IntegralComparison.Projective.TopTracePairing OAI.NumberTheory.PadicHodge.IntegralComparison.NegativeTwistResidueNaturality
variable {R : Type u} [CommRing R] [IsNoetherianRing R] [Module.Injective R R]
  [IsArtinianRing R] [IsLocalRing R] {n : ℕ}
attribute [local instance] MvPolynomial.gradedAlgebra
variable (X Y : Over (Spec (CommRingCat.of R))) [Nonempty X.left] (f : Y ⟶ X)
  [IsFinite f.left] [Etale f.left]
  (i : X ⟶ Projective.IntrinsicOverlap.Intrinsic.model R (n + 1)) [IsClosedImmersion i.left]
  (B : ℕ) (hB : n + 2 ≤ B) (g : ℕ)
  [SmoothOfRelativeDimension g X.hom] [IsProper X.hom] [GeometricallyConnected X.hom]

local instance composite_dimension : SmoothOfRelativeDimension g
    (i.left ≫ AlgebraicGeometry.SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.homogeneousProjπ (R := R) (σ := Fin (n + 2))) := by
  change SmoothOfRelativeDimension g (i.left ≫ (Projective.IntrinsicOverlap.Intrinsic.model R (n + 1)).hom)
  rw [Over.w i]
  infer_instance

include X i in
omit [Module.Injective R R] [IsArtinianRing R] [IsLocalRing R] [IsProper X.hom] [GeometricallyConnected X.hom] in
theorem degree : g + (n + 1 - g) = n + 1 := by
  have h := IntegralComparison.Smooth.ClosedDimension.projective i.left g
  simp only [Fintype.card_fin] at h
  omega

include X i in
omit [Module.Injective R R] [IsArtinianRing R] [IsLocalRing R] [IsProper X.hom] [GeometricallyConnected X.hom] in
theorem dimension_le : g ≤ n + 1 := Nat.le.intro (degree X i g)

local instance : (ProjectiveCoefficient.HomLocal.coefficient X f.left i).IsQuasicoherent :=
  Finite.MapPureTrace.coefficients_quasicoherent f.left i.left
local instance : (ProjectiveCoefficient.HomLocal.coefficient X f.left i).IsFiniteType :=
  Finite.MapPureTrace.coefficients_finiteType f.left i.left

abbrev cohomology : AddCommGrpCat.{u} :=
  (ProjectiveRefinement.Serre.cohomologyFunctor (R := R) (σ := Fin (n + 2)) g).obj
    (ProjectiveFinite.EtaleAdjunction.sourceForms X Y f i g)

def coefficientPairing := Projective.PureTrace.pairing (ProjectiveCoefficient.HomLocal.coefficient X f.left i)
  B n (Fintype.card_fin (n + 2)) hB (n + 1 - g)
  (Finite.MapCoefficientPurity.exactAt f.left i.left B n (Fintype.card_fin (n + 2)) hB g)
  g (degree X i g)

def coefficientTrace := SerreUnitTrace.trace (Projective.TopTracePairing.coefficientRing R)
  (coefficientPairing X Y f i B hB g)
  (Cech.StructurePullbackUnit.unit f.left i.left
    (AlgebraicGeometry.SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.homogeneousProjπ (R := R) (σ := Fin (n + 2)))
    (AlgebraicGeometry.SheafCohomology.Projective.StandardCech.MvPolynomial.coordinateOpenCover (R := R) (σ := Fin (n + 2)))
    (AlgebraicGeometry.SheafCohomology.Projective.StandardCech.MvPolynomial.iSup_coordinateOpenCover_eq_top (R := R) (σ := Fin (n + 2))))

def trace : cohomology X Y f i g ⟶ AddCommGrpCat.of (Projective.TopTracePairing.coefficientRing R) :=
  (ProjectiveRefinement.Serre.cohomologyFunctor (R := R) (σ := Fin (n + 2)) g).map
    (ProjectiveFinite.EtaleAdjunction.iso X Y f i g (NegativeTwistResidueNaturality.topChart.{u} (n + 1) (Fintype.card_fin (n + 2))) B hB (dimension_le X i g)).inv ≫
      coefficientTrace X Y f i B hB g

variable [IsProper Y.hom] [Smooth Y.hom] [GeometricallyConnected Y.hom]
  (s : Spec (CommRingCat.of R) ⟶ Y.left) (hs : s ≫ Y.hom = 𝟙 _)

local instance source_composite_proper : IsProper
    (f.left ≫ i.left ≫ AlgebraicGeometry.SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.homogeneousProjπ (R := R) (σ := Fin (n + 2))) := by
  change IsProper (f.left ≫ i.left ≫ (Projective.IntrinsicOverlap.Intrinsic.model R (n + 1)).hom)
  rw [Over.w i, Over.w f]
  infer_instance
local instance source_composite_smooth : Smooth
    (f.left ≫ i.left ≫ AlgebraicGeometry.SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.homogeneousProjπ (R := R) (σ := Fin (n + 2))) := by
  change Smooth (f.left ≫ i.left ≫ (Projective.IntrinsicOverlap.Intrinsic.model R (n + 1)).hom)
  rw [Over.w i, Over.w f]
  infer_instance
local instance source_composite_connected : GeometricallyConnected
    (f.left ≫ i.left ≫ AlgebraicGeometry.SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.homogeneousProjπ (R := R) (σ := Fin (n + 2))) := by
  change GeometricallyConnected (f.left ≫ i.left ≫ (Projective.IntrinsicOverlap.Intrinsic.model R (n + 1)).hom)
  rw [Over.w i, Over.w f]
  infer_instance

include hs in
omit [IsNoetherianRing R] [Module.Injective R R] [IsArtinianRing R] [IsLocalRing R] [Nonempty ↥X.left] [IsFinite (Over.Hom.left f)] [Etale (Over.Hom.left f)] [IsClosedImmersion (Over.Hom.left i)] [IsProper X.hom] [GeometricallyConnected X.hom] [IsProper Y.hom] [Smooth Y.hom] [GeometricallyConnected Y.hom] in
theorem section_over : s ≫ (f.left ≫ i.left ≫ AlgebraicGeometry.SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.homogeneousProjπ (R := R) (σ := Fin (n + 2))) = 𝟙 _ := by
  change s ≫ (f.left ≫ i.left ≫ (Projective.IntrinsicOverlap.Intrinsic.model R (n + 1)).hom) = 𝟙 _
  rw [Over.w i, Over.w f]
  exact hs

def coefficientUnitIso := IteratedCechStructureUnit.artinianIso f.left i.left
  (AlgebraicGeometry.SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.homogeneousProjπ (R := R) (σ := Fin (n + 2))) s (section_over X Y f i s hs)
  (AlgebraicGeometry.SheafCohomology.Projective.StandardCech.MvPolynomial.coordinateOpenCover (R := R) (σ := Fin (n + 2)))
  (AlgebraicGeometry.SheafCohomology.Projective.StandardCech.MvPolynomial.iSup_coordinateOpenCover_eq_top (R := R) (σ := Fin (n + 2)))

def traceIso : cohomology X Y f i g ≅ AddCommGrpCat.of (Projective.TopTracePairing.coefficientRing R) :=
  ((ProjectiveRefinement.Serre.cohomologyFunctor (R := R) (σ := Fin (n + 2)) g).mapIso
    (ProjectiveFinite.EtaleAdjunction.iso X Y f i g (NegativeTwistResidueNaturality.topChart.{u} (n + 1) (Fintype.card_fin (n + 2))) B hB (dimension_le X i g))).symm ≪≫
      SerreUnitTrace.traceIso (Projective.TopTracePairing.coefficientRing R) (coefficientPairing X Y f i B hB g)
        (coefficientUnitIso X Y f i s hs).toLinearEquiv

omit [GeometricallyConnected X.hom] in
theorem traceIso_hom : (traceIso X Y f i B hB g s hs).hom = trace X Y f i B hB g := by
  have hu := IteratedCechStructureUnit.artinianIso_one f.left i.left
    (AlgebraicGeometry.SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.homogeneousProjπ (R := R) (σ := Fin (n + 2))) s (section_over X Y f i s hs)
    (AlgebraicGeometry.SheafCohomology.Projective.StandardCech.MvPolynomial.coordinateOpenCover (R := R) (σ := Fin (n + 2)))
    (AlgebraicGeometry.SheafCohomology.Projective.StandardCech.MvPolynomial.iSup_coordinateOpenCover_eq_top (R := R) (σ := Fin (n + 2)))
  change _ ≫ (SerreUnitTrace.traceIso (Projective.TopTracePairing.coefficientRing R) (coefficientPairing X Y f i B hB g)
    (coefficientUnitIso X Y f i s hs).toLinearEquiv).hom = _
  rw [SerreUnitTrace.traceIso_hom]
  exact congrArg (fun v =>
    (ProjectiveRefinement.Serre.cohomologyFunctor (R := R) (σ := Fin (n + 2)) g).map
      (ProjectiveFinite.EtaleAdjunction.iso X Y f i g (NegativeTwistResidueNaturality.topChart.{u} (n + 1) (Fintype.card_fin (n + 2))) B hB (dimension_le X i g)).inv ≫
        SerreUnitTrace.trace (Projective.TopTracePairing.coefficientRing R) (coefficientPairing X Y f i B hB g) v) hu

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.FiniteEtale.ProperTraceBase

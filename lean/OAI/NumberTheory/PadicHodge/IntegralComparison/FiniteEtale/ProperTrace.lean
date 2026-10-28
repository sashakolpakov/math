import OAI.NumberTheory.PadicHodge.IntegralComparison.FiniteEtale.ProperTraceBase
import OAI.NumberTheory.PadicHodge.IntegralComparison.Projective.TraceAdjunctionNaturality

/-! # Proper Trace -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.FiniteEtale.ProperTrace

noncomputable section

/-! Finite étale transfer is compatible with the original proper source trace. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.MvPolynomial
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v

open OAI.NumberTheory.PadicHodge.IntegralComparison.Functor.TraceTransport

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

attribute [local instance] ProperTraceBase.composite_dimension

local instance : (ProjectiveCoefficient.HomLocal.coefficient X f.left i).IsQuasicoherent :=
  Finite.MapPureTrace.coefficients_quasicoherent f.left i.left
local instance : (ProjectiveCoefficient.HomLocal.coefficient X f.left i).IsFiniteType :=
  Finite.MapPureTrace.coefficients_finiteType f.left i.left

abbrev transfer_naturality := Projective.TraceAdjunctionNaturality.naturality
  (ProjectiveCoefficient.HomLocal.scalar X i) (ProjectiveCoefficient.HomLocal.coefficient X f.left i) B n (Fintype.card_fin (n + 2)) hB (n + 1 - g)
  (Smooth.ProjectiveSerre.exactAt i.left B n (Fintype.card_fin (n + 2)) hB g)
  (Finite.MapCoefficientPurity.exactAt f.left i.left B n (Fintype.card_fin (n + 2)) hB g)
  (Cech.StructurePullbackUnit.sheafMap f.left i.left) g (ProperTraceBase.degree X i g)
  (Cech.StructureUnit.unit i.left (AlgebraicGeometry.SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.homogeneousProjπ (R := R) (σ := Fin (n + 2)))
    (AlgebraicGeometry.SheafCohomology.Projective.StandardCech.MvPolynomial.coordinateOpenCover (R := R) (σ := Fin (n + 2)))
    (AlgebraicGeometry.SheafCohomology.Projective.StandardCech.MvPolynomial.iSup_coordinateOpenCover_eq_top (R := R) (σ := Fin (n + 2))))
  (Cech.StructurePullbackUnit.unit f.left i.left (AlgebraicGeometry.SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.homogeneousProjπ (R := R) (σ := Fin (n + 2)))
    (AlgebraicGeometry.SheafCohomology.Projective.StandardCech.MvPolynomial.coordinateOpenCover (R := R) (σ := Fin (n + 2)))
    (AlgebraicGeometry.SheafCohomology.Projective.StandardCech.MvPolynomial.iSup_coordinateOpenCover_eq_top (R := R) (σ := Fin (n + 2))))
  (Cech.StructurePullbackUnit.preserves_unit f.left i.left
    (AlgebraicGeometry.SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.homogeneousProjπ (R := R) (σ := Fin (n + 2)))
    (AlgebraicGeometry.SheafCohomology.Projective.StandardCech.MvPolynomial.coordinateOpenCover (R := R) (σ := Fin (n + 2)))
    (AlgebraicGeometry.SheafCohomology.Projective.StandardCech.MvPolynomial.iSup_coordinateOpenCover_eq_top (R := R) (σ := Fin (n + 2))))
  (ProjectiveCoefficient.HomLocal.formSheaf X i g) (ProjectiveFinite.EtaleAdjunction.sourceForms X Y f i g)
  (ProjectiveCoefficient.HomLocal.scalarAdjunction X i g (NegativeTwistResidueNaturality.topChart.{u} (n + 1) (Fintype.card_fin (n + 2))) B hB (ProperTraceBase.dimension_le X i g))
  (ProjectiveFinite.EtaleAdjunction.iso X Y f i g
    (NegativeTwistResidueNaturality.topChart.{u} (n + 1) (Fintype.card_fin (n + 2))) B hB (ProperTraceBase.dimension_le X i g))
  (AdjunctionTrace.trace X Y f i g)
  (AdjunctionTrace.normalization X Y f i g
    (NegativeTwistResidueNaturality.topChart.{u} (n + 1) (Fintype.card_fin (n + 2))) B hB (ProperTraceBase.dimension_le X i g))

omit [IsArtinianRing R] [IsLocalRing R] [GeometricallyConnected X.hom] in
theorem trace_transfer :
    (ProjectiveRefinement.Serre.cohomologyFunctor (R := R) (σ := Fin (n + 2)) g).map
        (AdjunctionTrace.trace X Y f i g) ≫
      Smooth.ProjectiveFormTrace.trace X i B hB g = ProperTraceBase.trace X Y f i B hB g :=
  transfer_naturality X Y f i B hB g

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.FiniteEtale.ProperTrace

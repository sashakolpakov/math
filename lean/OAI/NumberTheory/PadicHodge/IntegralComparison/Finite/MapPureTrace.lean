import OAI.NumberTheory.PadicHodge.IntegralComparison.Projective.PureTrace
import OAI.NumberTheory.PadicHodge.IntegralComparison.Smooth.ProjectiveSerre
import OAI.NumberTheory.PadicHodge.IntegralComparison.IteratedCechStructureUnit
import OAI.NumberTheory.PadicHodge.IntegralComparison.Finite.PushforwardCoherence

/-! # Map Pure Trace -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Finite.MapPureTrace

noncomputable section

/-! Pullback of functions along a finite map induces a map between the
actual dual resolutions. Evaluation on the actual unit commutes with
that map. Purity of the finite coefficient module is kept explicit here. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.MvPolynomial

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open OAI.NumberTheory.PadicHodge.IntegralComparison.Projective.TopTracePairing OAI.NumberTheory.PadicHodge.IntegralComparison.Cech.StructurePullbackUnit OAI.NumberTheory.PadicHodge.IntegralComparison.NegativeTwistResidueNaturality

universe u

section Coherence

variable {Y X Z : Scheme.{u}} (f : Y ⟶ X) [IsFinite f] (i : X ⟶ Z) [IsFinite i]

theorem coefficients_quasicoherent : (Cech.StructurePullbackUnit.coefficients f i).IsQuasicoherent := by
  let : (SheafOfModules.unit Y.ringCatSheaf).IsQuasicoherent :=
    AlgebraicGeometry.SheafCohomology.Projective.InvertibleFinitePresentation.invertible_quasicoherent AlgebraicGeometry.SheafCohomology.Projective.Invertible.Scheme.Modules.isInvertible_unit
  let : ((Scheme.Modules.pushforward f).obj (SheafOfModules.unit Y.ringCatSheaf)).IsQuasicoherent :=
    AlgebraicGeometry.SheafCohomology.Projective.Quasicoherent.Scheme.Modules.isQuasicoherent_pushforward_of_isAffineHom f
  exact AlgebraicGeometry.SheafCohomology.Projective.Quasicoherent.Scheme.Modules.isQuasicoherent_pushforward_of_isAffineHom i

theorem coefficients_finiteType : (Cech.StructurePullbackUnit.coefficients f i).IsFiniteType := by
  let : (SheafOfModules.unit Y.ringCatSheaf).IsQuasicoherent :=
    AlgebraicGeometry.SheafCohomology.Projective.InvertibleFinitePresentation.invertible_quasicoherent AlgebraicGeometry.SheafCohomology.Projective.Invertible.Scheme.Modules.isInvertible_unit
  let : (SheafOfModules.unit Y.ringCatSheaf).IsFiniteType := by
    have : (SheafOfModules.unit Y.ringCatSheaf).IsFinitePresentation :=
      AlgebraicGeometry.SheafCohomology.Projective.InvertibleFinitePresentation.invertible_finitePresentation AlgebraicGeometry.SheafCohomology.Projective.Invertible.Scheme.Modules.isInvertible_unit
    obtain ⟨q, hq⟩ := SheafOfModules.IsFinitePresentation.exists_quasicoherentData (SheafOfModules.unit Y.ringCatSheaf)
    refine { exists_localGeneratorsData := ⟨q.localGeneratorsData, ?_⟩ }
    constructor
    intro j
    exact (hq.isFinite_presentation j).isFiniteType_generators
  let : ((Scheme.Modules.pushforward f).obj (SheafOfModules.unit Y.ringCatSheaf)).IsQuasicoherent :=
    AlgebraicGeometry.SheafCohomology.Projective.Quasicoherent.Scheme.Modules.isQuasicoherent_pushforward_of_isAffineHom f
  let : ((Scheme.Modules.pushforward f).obj (SheafOfModules.unit Y.ringCatSheaf)).IsFiniteType :=
    PushforwardCoherence.finiteType f (SheafOfModules.unit Y.ringCatSheaf)
  exact PushforwardCoherence.finiteType i _

end Coherence

variable {R : Type u} [CommRing R] [IsNoetherianRing R] [Module.Injective R R]
  {σ : Type} [Fintype σ] [LinearOrder σ]

attribute [local instance] MvPolynomial.gradedAlgebra

variable {Y X : Scheme.{u}} [Nonempty X]
  (f : Y ⟶ X) [IsFinite f]
  (i : X ⟶ Proj (homogeneousSubmodule σ R)) [IsClosedImmersion i]
  (B n : ℕ) (hn : Fintype.card σ = n + 2) (hB : n + 2 ≤ B)
  (g : ℕ) [SmoothOfRelativeDimension g (i ≫ AlgebraicGeometry.SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.homogeneousProjπ)]

local instance : (Cech.StructurePullbackUnit.coefficients f i).IsQuasicoherent := coefficients_quasicoherent f i
local instance : (Cech.StructurePullbackUnit.coefficients f i).IsFiniteType := coefficients_finiteType f i

variable (hPure : ∀ q, q ≠ n + 1 - g →
  (ProjectiveRefinement.Serre.fixedDual (Cech.StructurePullbackUnit.coefficients f i) B n hn).ExactAt q)

theorem naturality :
    let M := Projective.ClosedImmersionPurity.directImage i;
    let C := Cech.StructurePullbackUnit.coefficients f i;
    let hM := Smooth.ProjectiveSerre.exactAt i B n hn hB g;
    let hdim : g + (n + 1 - g) = n + 1 := by
      have h := Smooth.ClosedDimension.projective i g
      omega;
    let vM := Cech.StructureUnit.unit i (AlgebraicGeometry.SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.homogeneousProjπ (R := R) (σ := σ))
      (AlgebraicGeometry.SheafCohomology.Projective.StandardCech.MvPolynomial.coordinateOpenCover (R := R) (σ := σ)) (AlgebraicGeometry.SheafCohomology.Projective.StandardCech.MvPolynomial.iSup_coordinateOpenCover_eq_top (R := R) (σ := σ));
    let vC := Cech.StructurePullbackUnit.unit f i (AlgebraicGeometry.SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.homogeneousProjπ (R := R) (σ := σ))
      (AlgebraicGeometry.SheafCohomology.Projective.StandardCech.MvPolynomial.coordinateOpenCover (R := R) (σ := σ)) (AlgebraicGeometry.SheafCohomology.Projective.StandardCech.MvPolynomial.iSup_coordinateOpenCover_eq_top (R := R) (σ := σ));
    let a := Projective.NegativeRefinement.leftHom M C (NegativeTwistResidueNaturality.topChart.{u} (n + 1) hn) B (Cech.StructurePullbackUnit.sheafMap f i);
    let b := Projective.NegativeRefinement.rightHom M C (NegativeTwistResidueNaturality.topChart.{u} (n + 1) hn) B (Cech.StructurePullbackUnit.sheafMap f i);
    let : QuasiIso ((Affine.LocalDualInvariance.functor (Projective.TopTracePairing.canonicalTwist (R := R) n hn)).map
      a.chainMap.op) := ProjectiveRefinement.DualMap.left_quasiIso M C
        (NegativeTwistResidueNaturality.topChart.{u} (n + 1) hn) B (n + 2) hB (Cech.StructurePullbackUnit.sheafMap f i);
    let : IsIso (HomologicalComplex.homologyMap
      ((Affine.LocalDualInvariance.functor (Projective.TopTracePairing.canonicalTwist (R := R) n hn)).map a.chainMap.op) (n + 1 - g)) :=
      (isoOfQuasiIsoAt
        ((Affine.LocalDualInvariance.functor (Projective.TopTracePairing.canonicalTwist (R := R) n hn)).map a.chainMap.op) (n + 1 - g)).isIso_hom;
    (Trace.PureFunctorNaturality.cohomologyFunctor (AlgebraicGeometry.SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.homogeneousProjπ (R := R) (σ := σ))
      (AlgebraicGeometry.SheafCohomology.Projective.StandardCech.MvPolynomial.coordinateOpenCover (R := R) (σ := σ)) g).map
        (Trace.PureRefinement.map (Projective.TopTracePairing.canonicalTwist (R := R) n hn) a.chainMap b.chainMap (n + 1 - g)) ≫
      Projective.PureTrace.trace M B n hn hB (n + 1 - g) hM g hdim vM =
      Projective.PureTrace.trace C B n hn hB (n + 1 - g) hPure g hdim vC := by
  exact Projective.PureTrace.naturality
    (Projective.ClosedImmersionPurity.directImage i) B n hn hB (n + 1 - g)
    (Smooth.ProjectiveSerre.exactAt i B n hn hB g)
    (Cech.StructurePullbackUnit.coefficients f i) hPure (Cech.StructurePullbackUnit.sheafMap f i) g
    (by
      have h := Smooth.ClosedDimension.projective i g
      omega)
    (Cech.StructureUnit.unit i (AlgebraicGeometry.SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.homogeneousProjπ (R := R) (σ := σ))
      (AlgebraicGeometry.SheafCohomology.Projective.StandardCech.MvPolynomial.coordinateOpenCover (R := R) (σ := σ))
      (AlgebraicGeometry.SheafCohomology.Projective.StandardCech.MvPolynomial.iSup_coordinateOpenCover_eq_top (R := R) (σ := σ)))
    (Cech.StructurePullbackUnit.unit f i (AlgebraicGeometry.SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.homogeneousProjπ (R := R) (σ := σ))
      (AlgebraicGeometry.SheafCohomology.Projective.StandardCech.MvPolynomial.coordinateOpenCover (R := R) (σ := σ))
      (AlgebraicGeometry.SheafCohomology.Projective.StandardCech.MvPolynomial.iSup_coordinateOpenCover_eq_top (R := R) (σ := σ)))
    (Cech.StructurePullbackUnit.preserves_unit f i (AlgebraicGeometry.SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.homogeneousProjπ (R := R) (σ := σ))
      (AlgebraicGeometry.SheafCohomology.Projective.StandardCech.MvPolynomial.coordinateOpenCover (R := R) (σ := σ))
      (AlgebraicGeometry.SheafCohomology.Projective.StandardCech.MvPolynomial.iSup_coordinateOpenCover_eq_top (R := R) (σ := σ)))

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Finite.MapPureTrace

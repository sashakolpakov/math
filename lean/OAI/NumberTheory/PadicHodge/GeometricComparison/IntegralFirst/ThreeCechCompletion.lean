import OAI.NumberTheory.PadicHodge.GeometricComparison.IntegralFirst.ThreeCechRegularity
import OAI.NumberTheory.PadicHodge.GeometricComparison.IntegralFirst.ThreeCechFiniteness
import OAI.NumberTheory.PadicHodge.GeometricComparison.CochainQuotientCohomology
import OAI.NumberTheory.PadicHodge.GeometricComparison.Integral.GlobalOneBaseChange
import OAI.AlgebraicGeometry.Crystalline.Cohomology.Finite.ModuleAdicCompleteness

/-! # Three Cech Completion -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.IntegralFirst.ThreeCechCompletion.IntegralFirstThreeCechCompletion

noncomputable section

/-! Actual integral three-term Čech cohomology agrees with its compatible coefficient-power quotients. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

variable (R : Type) [CommRing R] [IsNoetherianRing R]
  (X : Over (Spec (CommRingCat.of R))) [IsProper X.hom] [Smooth X.hom]
  {ι : Type} [Finite ι] (U : ι → X.left.Opens)
  (hU : ∀ i, IsAffineOpen (U i)) (hcover : iSup U = ⊤)

def complex : CochainComplex (ModuleCat.{0} R) ℕ :=
  (IntegralAffine.CechCoordinateUnit.IntegralAffineCechCoordinateUnit.bicomplex R X U).total (.up ℕ)

omit [Finite ι] in
include hU hcover in
theorem cohomology_finite (n : ℕ) (hn : n ≤ 2) :
    Module.Finite R ((complex R X U).homology n) := by
  let : Module.Finite R (((IntrinsicCech.CechBicomplex.IntrinsicCechBicomplex.bicomplex R X U
      (FirstThree.ThreeComplex.FirstThreeComplex.complex (AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.sheafComplex R X))).total (.up ℕ)).homology n) :=
    ThreeCechFiniteness.IntegralFirstThreeCechFiniteness.total_finite R X U hU hcover n hn
  exact Module.Finite.equiv (HomologicalComplex.homologyMapIso
    (HomologicalComplex₂.total.mapIso (IntegralAffine.CechCoordinateUnit.IntegralAffineCechCoordinateUnit.iso R X U hU) (.up ℕ)) n).symm.toLinearEquiv

variable (r : R) (hr : IsRegular r) [IsAdicComplete (Ideal.span {r}) R]

def compatible (i : ℕ) := AdicCohomology.AdicCohomologyLimit.compatible
  (fun n => CochainQuotientCohomology.PrincipalCochainQuotient.cohomology R (complex R X U) r n i)
  (CochainQuotientCohomology.PrincipalCochainQuotient.cohomologyTransition R (complex R X U) r i)

def equiv (i : ℕ) (hi : i ≤ 1) : (complex R X U).homology i ≃ₗ[R] compatible R X U r i := by
  let : Module.Finite R ((complex R X U).homology i) := cohomology_finite R X U hU hcover i (by omega)
  let : Module.Finite R ((complex R X U).homology (i + 1)) :=
    cohomology_finite R X U hU hcover (i + 1) (by omega)
  exact (AlgebraicGeometry.Crystalline.Cohomology.Finite.ModuleAdicCompleteness.FiniteModuleAdicCompleteness.equiv R (Ideal.span {r}) ((complex R X U).homology i)).trans
    (CochainQuotientCohomology.PrincipalCochainQuotient.completionEquiv R (complex R X U) r
      (ThreeCechRegularity.IntegralFirstThreeCechRegularity.total_regular R X U hU r hr) i)

omit [Finite ι] in
theorem equiv_eval (i : ℕ) (hi : i ≤ 1) (x : (complex R X U).homology i) (n : ℕ) :
    (IntegralFirstThreeCechCompletion.equiv R X U hU hcover r hr i hi x).val n =
      CochainQuotientCohomology.PrincipalCochainQuotient.reduction R (complex R X U) r n i x := by
  let : Module.Finite R ((complex R X U).homology i) := cohomology_finite R X U hU hcover i (by omega)
  let : Module.Finite R ((complex R X U).homology (i + 1)) :=
    cohomology_finite R X U hU hcover (i + 1) (by omega)
  change (CochainQuotientCohomology.PrincipalCochainQuotient.completionEquiv R (complex R X U) r
    (ThreeCechRegularity.IntegralFirstThreeCechRegularity.total_regular R X U hU r hr) i
      (AlgebraicGeometry.Crystalline.Cohomology.Finite.ModuleAdicCompleteness.FiniteModuleAdicCompleteness.equiv R (Ideal.span {r}) ((complex R X U).homology i) x)).val n = _
  erw [AlgebraicGeometry.Crystalline.Cohomology.Finite.ModuleAdicCompleteness.FiniteModuleAdicCompleteness.equiv_apply, CochainQuotientCohomology.PrincipalCochainQuotient.completionEquiv_of]

variable [Module.Flat ℤ R]

def nativeHoneEquiv : AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.cohomology R X 1 ≃ₗ[R] compatible R X U r 1 :=
  ((Integral.GlobalOneBaseChange.IntegralGlobalHOneBaseChange.coordinateEquiv R X U hU hcover).symm.trans
    (((complex R X U).extendHomologyIso ComplexShape.embeddingUpNat (j := 1) rfl).toLinearEquiv)).trans
      (IntegralFirstThreeCechCompletion.equiv R X U hU hcover r hr 1 le_rfl)

end

end OAI.NumberTheory.PadicHodge.GeometricComparison.IntegralFirst.ThreeCechCompletion.IntegralFirstThreeCechCompletion

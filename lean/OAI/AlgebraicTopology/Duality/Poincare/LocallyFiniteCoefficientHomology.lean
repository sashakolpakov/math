import OAI.AlgebraicTopology.Duality.Poincare.LocallyFiniteCoefficients
import OAI.AlgebraicTopology.Duality.Poincare.IntegralHomologyCoefficients

/-! # Locally Finite Coefficient Homology -/

namespace OAI.AlgebraicTopology.Duality.Poincare.LocallyFiniteCoefficientHomology

noncomputable section

/-!
# Finite and locally finite coefficient change on native homology

The restriction-of-scalars homology comparison sends a represented cycle to
the same represented cycle. This fixes the meaning of the locally finite
coefficient map and gives its compatibility with finite ordinary homology.
-/

open _root_.CategoryTheory _root_.CategoryTheory.Limits

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- The given rational complex, regarded as an integer complex. -/
abbrev restrictRationalChainComplex (C : ChainComplex (ModuleCat.{0} ℚ) ℕ) :
    ChainComplex (ModuleCat.{0} ℤ) ℕ :=
  ((ModuleCat.restrictScalars (Int.castRingHom ℚ)).mapHomologicalComplex
    (ComplexShape.down ℕ)).obj C

/-- Restriction of scalars changes no coefficient of a cycle. -/
def rationalCycleOfRestricted (C : ChainComplex (ModuleCat.{0} ℚ) ℕ) (n : ℕ)
    (z : Cohomology.Singular.ChainRepresentatives.chainCycles (restrictRationalChainComplex C) n) : Cohomology.Singular.ChainRepresentatives.chainCycles C n :=
  ⟨z.val, z.property⟩

@[simp]
theorem rationalCycleOfRestricted_val (C : ChainComplex (ModuleCat.{0} ℚ) ℕ) (n : ℕ)
    (z : Cohomology.Singular.ChainRepresentatives.chainCycles (restrictRationalChainComplex C) n) :
    (rationalCycleOfRestricted C n z).val = z.val := rfl

/-- The standard homology comparison for restriction of rational scalars. -/
def rationalChainHomologyRestrictIso (C : ChainComplex (ModuleCat.{0} ℚ) ℕ) (n : ℕ) :
    (restrictRationalChainComplex C).homology n ≅
      (ModuleCat.restrictScalars (Int.castRingHom ℚ)).obj (C.homology n) :=
  (C.sc n).mapHomologyIso (ModuleCat.restrictScalars (Int.castRingHom ℚ))

/-- The canonical comparison really keeps the class of each actual cycle. -/
theorem rationalChainHomologyRestrictIso_chainClass
    (C : ChainComplex (ModuleCat.{0} ℚ) ℕ) (n : ℕ)
    (z : Cohomology.Singular.ChainRepresentatives.chainCycles (restrictRationalChainComplex C) n) :
    (rationalChainHomologyRestrictIso C n).hom
        (Cohomology.Singular.ChainRepresentatives.chainClass (restrictRationalChainComplex C) n z) =
      Cohomology.Singular.ChainRepresentatives.chainClass C n (rationalCycleOfRestricted C n z) := by
  let S := C.sc n
  let F := ModuleCat.restrictScalars (Int.castRingHom ℚ)
  let d := S.moduleCatLeftHomologyData
  let k := ((restrictRationalChainComplex C).sc n).moduleCatCyclesIso.inv z
  have hk : (d.map F).cyclesIso.hom k = rationalCycleOfRestricted C n z := by
    apply Subtype.ext
    have hi := ConcreteCategory.congr_hom ((d.map F).cyclesIso_hom_comp_i) k
    have hi' := ConcreteCategory.congr_hom
      (((restrictRationalChainComplex C).sc n).moduleCatCyclesIso_inv_iCycles) z
    exact hi.trans hi'
  rw [Cohomology.Singular.ChainRepresentatives.chainClass_eq_homologyπ]
  change (S.mapHomologyIso F).hom ((S.map F).homologyπ k) = _
  rw [d.mapHomologyIso_eq F]
  change (F.map d.homologyIso.inv)
      ((d.map F).homologyIso.hom ((S.map F).homologyπ k)) = _
  have hp := ConcreteCategory.congr_hom
    ((d.map F).homologyπ_comp_homologyIso_hom) k
  calc
    _ = (F.map d.homologyIso.inv)
        ((d.map F).π ((d.map F).cyclesIso.hom k)) :=
      congrArg (fun q => (F.map d.homologyIso.inv) q) hp
    _ = (F.map d.homologyIso.inv)
        ((d.map F).π (rationalCycleOfRestricted C n z)) :=
      congrArg (fun q => (F.map d.homologyIso.inv) ((d.map F).π q)) hk
    _ = _ := rfl

/-- An actual locally finite integral cycle, with the same coefficients in `ℚ`. -/
def locallyFiniteIntegralToRationalCycles (X : TopCat.{0}) (n : ℕ)
    (z : Cohomology.Singular.ChainRepresentatives.chainCycles (AlgebraicGeometry.CycleClass.Geometric.LocallyFiniteComplex.Cycles.locallyFiniteSingularComplex ℤ X) n) :
    Cohomology.Singular.ChainRepresentatives.chainCycles (AlgebraicGeometry.CycleClass.Geometric.LocallyFiniteComplex.Cycles.locallyFiniteSingularComplex ℚ X) n :=
  rationalCycleOfRestricted (AlgebraicGeometry.CycleClass.Geometric.LocallyFiniteComplex.Cycles.locallyFiniteSingularComplex ℚ X) n
    (Cohomology.Singular.EvaluationNaturality.chainCycleMap (LocallyFiniteCoefficients.locallyFiniteIntegralToRationalChainMap X) n z)

@[simp]
theorem locallyFiniteIntegralToRationalCycles_val (X : TopCat.{0}) (n : ℕ)
    (z : Cohomology.Singular.ChainRepresentatives.chainCycles (AlgebraicGeometry.CycleClass.Geometric.LocallyFiniteComplex.Cycles.locallyFiniteSingularComplex ℤ X) n) :
    (locallyFiniteIntegralToRationalCycles X n z).val =
      LocallyFiniteCoefficients.locallyFiniteIntegralToRational X n z.val := rfl

/-- The native homology map sends each locally finite cycle class to its
literal rational coefficient change. -/
theorem locallyFiniteIntegralToRationalHomology_chainClass (X : TopCat.{0}) (n : ℕ)
    (z : Cohomology.Singular.ChainRepresentatives.chainCycles (AlgebraicGeometry.CycleClass.Geometric.LocallyFiniteComplex.Cycles.locallyFiniteSingularComplex ℤ X) n) :
    LocallyFiniteCoefficients.locallyFiniteIntegralToRationalHomology X n
        (Cohomology.Singular.ChainRepresentatives.chainClass (AlgebraicGeometry.CycleClass.Geometric.LocallyFiniteComplex.Cycles.locallyFiniteSingularComplex ℤ X) n z) =
      Cohomology.Singular.ChainRepresentatives.chainClass (AlgebraicGeometry.CycleClass.Geometric.LocallyFiniteComplex.Cycles.locallyFiniteSingularComplex ℚ X) n
        (locallyFiniteIntegralToRationalCycles X n z) := by
  change (LocallyFiniteCoefficients.locallyFiniteRationalHomologyRestrictIso X n).hom
      (HomologicalComplex.homologyMap (LocallyFiniteCoefficients.locallyFiniteIntegralToRationalChainMap X) n
        (Cohomology.Singular.ChainRepresentatives.chainClass (AlgebraicGeometry.CycleClass.Geometric.LocallyFiniteComplex.Cycles.locallyFiniteSingularComplex ℤ X) n z)) = _
  rw [Cohomology.Singular.EvaluationNaturality.chainClass_naturality]
  exact rationalChainHomologyRestrictIso_chainClass
    (AlgebraicGeometry.CycleClass.Geometric.LocallyFiniteComplex.Cycles.locallyFiniteSingularComplex ℚ X) n
    (Cohomology.Singular.EvaluationNaturality.chainCycleMap (LocallyFiniteCoefficients.locallyFiniteIntegralToRationalChainMap X) n z)

/-- Finite-cycle inclusion and rational coefficient change commute before
passing to the native homology classes. -/
theorem locallyFiniteIntegralToRationalCycles_ordinary (X : TopCat.{0}) (n : ℕ)
    (z : Cohomology.Singular.ChainRepresentatives.chainCycles (AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.integralSingularChains X) n) :
    locallyFiniteIntegralToRationalCycles X n
        (Cohomology.Singular.EvaluationNaturality.chainCycleMap (AlgebraicGeometry.CycleClass.Geometric.LocallyFiniteComparison.Cycles.ordinaryToLocallyFiniteChainMap ℤ X) n z) =
      Cohomology.Singular.EvaluationNaturality.chainCycleMap (AlgebraicGeometry.CycleClass.Geometric.LocallyFiniteComparison.Cycles.ordinaryToLocallyFiniteChainMap ℚ X) n
        (IntegralHomologyCoefficients.integralToScalarSingularCycles (R := ℚ) X n z) := by
  apply Subtype.ext
  exact LocallyFiniteCoefficients.locallyFiniteIntegralToRational_ordinary X n z.val

/-- Rationalization commutes with the actual ordinary-to-locally-finite
singular homology map. Compactness is not needed for this square. -/
theorem locallyFiniteIntegralToRationalHomology_ordinary (X : TopCat.{0}) (n : ℕ)
    (z : (AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.integralSingularChains X).homology n) :
    LocallyFiniteCoefficients.locallyFiniteIntegralToRationalHomology X n
        (HomologicalComplex.homologyMap (AlgebraicGeometry.CycleClass.Geometric.LocallyFiniteComparison.Cycles.ordinaryToLocallyFiniteChainMap ℤ X) n z) =
      HomologicalComplex.homologyMap (AlgebraicGeometry.CycleClass.Geometric.LocallyFiniteComparison.Cycles.ordinaryToLocallyFiniteChainMap ℚ X) n
        (IntegralHomologyCoefficients.integralToScalarSingularHomology (R := ℚ) X n z) := by
  obtain ⟨c, rfl⟩ := Cohomology.Singular.ChainRepresentatives.chainClass_surjective (AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.integralSingularChains X) n z
  calc
    _ = LocallyFiniteCoefficients.locallyFiniteIntegralToRationalHomology X n
        (Cohomology.Singular.ChainRepresentatives.chainClass (AlgebraicGeometry.CycleClass.Geometric.LocallyFiniteComplex.Cycles.locallyFiniteSingularComplex ℤ X) n
          (Cohomology.Singular.EvaluationNaturality.chainCycleMap (AlgebraicGeometry.CycleClass.Geometric.LocallyFiniteComparison.Cycles.ordinaryToLocallyFiniteChainMap ℤ X) n c)) :=
      congrArg (LocallyFiniteCoefficients.locallyFiniteIntegralToRationalHomology X n)
        (Cohomology.Singular.EvaluationNaturality.chainClass_naturality (AlgebraicGeometry.CycleClass.Geometric.LocallyFiniteComparison.Cycles.ordinaryToLocallyFiniteChainMap ℤ X) n c)
    _ = Cohomology.Singular.ChainRepresentatives.chainClass (AlgebraicGeometry.CycleClass.Geometric.LocallyFiniteComplex.Cycles.locallyFiniteSingularComplex ℚ X) n
        (locallyFiniteIntegralToRationalCycles X n
          (Cohomology.Singular.EvaluationNaturality.chainCycleMap (AlgebraicGeometry.CycleClass.Geometric.LocallyFiniteComparison.Cycles.ordinaryToLocallyFiniteChainMap ℤ X) n c)) :=
      locallyFiniteIntegralToRationalHomology_chainClass X n _
    _ = Cohomology.Singular.ChainRepresentatives.chainClass (AlgebraicGeometry.CycleClass.Geometric.LocallyFiniteComplex.Cycles.locallyFiniteSingularComplex ℚ X) n
        (Cohomology.Singular.EvaluationNaturality.chainCycleMap (AlgebraicGeometry.CycleClass.Geometric.LocallyFiniteComparison.Cycles.ordinaryToLocallyFiniteChainMap ℚ X) n
          (IntegralHomologyCoefficients.integralToScalarSingularCycles (R := ℚ) X n c)) :=
      congrArg (Cohomology.Singular.ChainRepresentatives.chainClass (AlgebraicGeometry.CycleClass.Geometric.LocallyFiniteComplex.Cycles.locallyFiniteSingularComplex ℚ X) n)
        (locallyFiniteIntegralToRationalCycles_ordinary X n c)
    _ = HomologicalComplex.homologyMap (AlgebraicGeometry.CycleClass.Geometric.LocallyFiniteComparison.Cycles.ordinaryToLocallyFiniteChainMap ℚ X) n
        (Cohomology.Singular.ChainRepresentatives.chainClass (Cohomology.Singular.Evaluation.singularScalarChains (R := ℚ) X) n
          (IntegralHomologyCoefficients.integralToScalarSingularCycles (R := ℚ) X n c)) :=
      (Cohomology.Singular.EvaluationNaturality.chainClass_naturality (AlgebraicGeometry.CycleClass.Geometric.LocallyFiniteComparison.Cycles.ordinaryToLocallyFiniteChainMap ℚ X) n _).symm
    _ = _ := congrArg
      (HomologicalComplex.homologyMap (AlgebraicGeometry.CycleClass.Geometric.LocallyFiniteComparison.Cycles.ordinaryToLocallyFiniteChainMap ℚ X) n)
      (IntegralHomologyCoefficients.integralToScalarSingularHomology_chainClass (R := ℚ) X n c).symm

end

end OAI.AlgebraicTopology.Duality.Poincare.LocallyFiniteCoefficientHomology

import OAI.AlgebraicGeometry.CycleClass.Geometric.NormalChartPurity
import OAI.AlgebraicGeometry.CycleClass.Geometric.ComplexLocalPurityNaturality

/-! # Immersion Normal Fin -/

namespace OAI.AlgebraicGeometry.CycleClass.Geometric.ImmersionNormalFin

noncomputable section

/-!
# The actual normal class in the explicit degree `2p`

For the normal space `Fin p → ℂ`, this file transports the existing normalized
class along the proved dimension equality. Coordinate independence then
identifies it with the standard normal generator, including when `p = 0`.
-/

open _root_.CategoryTheory _root_.CategoryTheory.Limits

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Cycles

/-- Identity coordinates give precisely the standard normalized rational
normal class. -/
theorem complexCoordinateLocalClass_refl (p : ℕ) :
    ComplexLocalPurityNaturality.Cycles.complexCoordinateLocalClass (ContinuousLinearEquiv.refl ℂ (Fin p → ℂ)) =
      RationalLocalPurity.Cycles.complexNormalRationalDualClass p := by
  unfold ComplexLocalPurityNaturality.Cycles.complexCoordinateLocalClass
  rw [FiniteComplexLocalPurity.Cycles.complexLinearLocalCohomologyIso_hom]
  change AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomologyMap (ModuleCat.of ℚ ℚ) (𝟙 (TopCat.of (Fin p → ℂ)))
    (fun _ hx => hx) (2 * p) ((RationalLocalPurity.Cycles.complexNormalRationalTopCohomologyIso p).inv 1) = _
  rw [AlgebraicTopology.Cohomology.Singular.RelativeOpenSupport.relativeSingularCohomologyMap_id]
  rfl

/-- Explicit degree transport identifies the existing finite-dimensional
normal class with the standard class in degree `2p`. -/
theorem finiteComplexLocalClass_fin (p : ℕ) :
    (eqToHom (congrArg (fun n => FiniteComplexLocalPurity.Cycles.finiteComplexLocalCohomology (Fin p → ℂ) (2 * n))
      (Module.finrank_fin_fun ℂ : Module.finrank ℂ (Fin p → ℂ) = p)))
        (FiniteComplexLocalPurity.Cycles.finiteComplexLocalClass (Fin p → ℂ)) = RationalLocalPurity.Cycles.complexNormalRationalDualClass p := by
  rw [ComplexLocalPurityNaturality.Cycles.finiteComplexLocalClass_eq_coordinate]
  exact (ComplexLocalPurityNaturality.Cycles.complexCoordinateLocalClass_cast (Module.finrank_fin_fun ℂ)
    (FiniteComplexLocalPurity.Cycles.finiteComplexCoordinates (Fin p → ℂ))).trans
      ((ComplexLocalPurityNaturality.Cycles.complexCoordinateLocalClass_eq _ (ContinuousLinearEquiv.refl ℂ (Fin p → ℂ))).trans
        (complexCoordinateLocalClass_refl p))

end Cycles

namespace Analytic.ImmersionNormalPair

open OAI.AlgebraicGeometry.CycleClass.Geometric.ImmersionNormalFin.Cycles

variable {M N E : Type} [TopologicalSpace N]
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  {f : M → N} {x : M} {p : ℕ} (P : ComplexPoints.Analytic.NormalPairRecenter.ImmersionNormalPair E (Fin p → ℂ) f x)

/-- The existing normal-pair class, transported only along the proved
identity `finrank ℂ (Fin p → ℂ) = p`. -/
def _root_.OAI.AlgebraicGeometry.ComplexPoints.Analytic.NormalPairRecenter.ImmersionNormalPair.rationalClassFin : P.relativeCohomology (ModuleCat.of ℚ ℚ) (2 * p) :=
  (eqToHom (congrArg (fun n => P.relativeCohomology (ModuleCat.of ℚ ℚ) (2 * n))
    (Module.finrank_fin_fun ℂ : Module.finrank ℂ (Fin p → ℂ) = p))) P.rationalClass

omit [NormedSpace ℝ E] in
private theorem normalCohomologyMap_degree_transport {a b : ℕ} (h : a = b)
    (c : FiniteComplexLocalPurity.Cycles.finiteComplexLocalCohomology (Fin p → ℂ) (2 * a)) :
    (eqToHom (congrArg (fun n => P.relativeCohomology (ModuleCat.of ℚ ℚ) (2 * n)) h))
        (P.normalCohomologyMap (ModuleCat.of ℚ ℚ) (2 * a) c) =
      P.normalCohomologyMap (ModuleCat.of ℚ ℚ) (2 * b)
        ((eqToHom (congrArg (fun n => FiniteComplexLocalPurity.Cycles.finiteComplexLocalCohomology (Fin p → ℂ) (2 * n)) h)) c) := by
  subst b
  rfl

/-- The explicit-degree class is the actual normal-coordinate pullback
of the established standard rational normal class. -/
theorem _root_.OAI.AlgebraicGeometry.ComplexPoints.Analytic.NormalPairRecenter.ImmersionNormalPair.rationalClassFin_eq_normalPullback :
    P.rationalClassFin = P.normalCohomologyMap (ModuleCat.of ℚ ℚ) (2 * p)
      (RationalLocalPurity.Cycles.complexNormalRationalDualClass p) := by
  unfold ComplexPoints.Analytic.NormalPairRecenter.ImmersionNormalPair.rationalClassFin
  rw [P.rationalClass_eq_pullback,
    (normalCohomologyMap_degree_transport P) (Module.finrank_fin_fun ℂ),
    Cycles.finiteComplexLocalClass_fin]

/-- The explicit-degree class respects actual shrinking in one normal
coordinate chart. -/
theorem _root_.OAI.AlgebraicGeometry.ComplexPoints.Analytic.NormalPairRecenter.ImmersionNormalPair.rationalClassFin_restrict (Q : ComplexPoints.Analytic.NormalPairRecenter.ImmersionNormalPair E (Fin p → ℂ) f x)
    (hQP : Q.neighborhood ⊆ P.neighborhood) (hchart : Q.ambientChart = P.ambientChart) :
    RelativeCohomologyExcision.Cycles.supportNeighborhoodCohomologyRestriction (TopCat.of N) hQP (Set.range f) (2 * p)
      P.rationalClassFin = Q.rationalClassFin := by
  rw [P.rationalClassFin_eq_normalPullback, Q.rationalClassFin_eq_normalPullback]
  exact ConcreteCategory.congr_hom (P.normalCohomologyMap_restrict Q hQP hchart (2 * p))
    (RationalLocalPurity.Cycles.complexNormalRationalDualClass p)

end Analytic.ImmersionNormalPair

end

end OAI.AlgebraicGeometry.CycleClass.Geometric.ImmersionNormalFin

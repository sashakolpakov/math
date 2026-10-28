import OAI.AlgebraicGeometry.CycleClass.Geometric.RealComplexNormalModel
import OAI.AlgebraicGeometry.CycleClass.Geometric.SphereHomologyInduction
import OAI.AlgebraicGeometry.CycleClass.Geometric.Point

/-! # Complex Local Top Homology -/

namespace OAI.AlgebraicGeometry.CycleClass.Geometric.ComplexLocalTopHomology.Cycles

noncomputable section

/-!
# Top local homology of complex normal coordinates

The group here is the homology of the actual relative singular-chain complex
for `(ℂ^p, ℂ^p \ {0})`. The relative boundary, the explicit interleaved real
coordinates, radial retraction, and the computed ordinary sphere homology
give an isomorphism from its degree `2p` group to `ℤ`.

The resulting coordinate isomorphism is specified by these maps. Compatibility
with complex orientations or changes of normal charts is a separate theorem;
it is not asserted by this rank calculation.
-/

open _root_.CategoryTheory _root_.CategoryTheory.Limits

/-- Local homology of positive-dimensional complex coordinates reduces to the
standard real sphere of dimension one less than their real dimension. -/
def positiveComplexNormalLocalStandardSphereIso (p n : ℕ) (hn : n ≠ 0) :
    LocalHomology.Cycles.localSingularHomology (TopCat.of (Fin (p + 1) → ℂ)) 0 (n + 1) ≅
      SphereHomologyInduction.Cycles.standardSphereHomology (2 * p + 1) n := by
  have hdim : 2 * (p + 1) = 2 * p + 1 + 1 := by omega
  simpa only [hdim] using RealComplexNormalModel.Cycles.complexNormalLocalRealSphereIso (p + 1) n hn

/-- In positive complex dimension the actual top local homology is `ℤ`.
The map uses the relative boundary and the computed ordinary sphere homology. -/
def positiveComplexNormalTopLocalHomologyIso (p : ℕ) :
    LocalHomology.Cycles.localSingularHomology (TopCat.of (Fin (p + 1) → ℂ)) 0 (2 * p + 2) ≅
      ModuleCat.of ℤ ℤ :=
  positiveComplexNormalLocalStandardSphereIso p (2 * p + 1)
      (Nat.succ_ne_zero (2 * p)) ≪≫
    SphereHomologyInduction.Cycles.standardSphereTopHomologyIso (2 * p)

/-- The actual top local integral homology of `ℂ^p` is isomorphic to `ℤ`,
including the separately established dimension-zero point normalization. -/
def complexNormalTopLocalHomologyIso (p : ℕ) :
    LocalHomology.Cycles.localSingularHomology (TopCat.of (Fin p → ℂ)) 0 (2 * p) ≅ ModuleCat.of ℤ ℤ := by
  cases p with
  | zero => exact Point.Cycles.complexZeroLocalHomologyIso
  | succ p =>
      simpa only [Nat.mul_succ] using positiveComplexNormalTopLocalHomologyIso p

/-- The same top local homology calculation as an isomorphism of `ℤ`-modules. -/
def complexNormalTopLocalHomologyEquiv (p : ℕ) :
    LocalHomology.Cycles.localSingularHomology (TopCat.of (Fin p → ℂ)) 0 (2 * p) ≃ₗ[ℤ] ℤ :=
  (complexNormalTopLocalHomologyIso p).toLinearEquiv

/-- The top local homology module has rank one. No orientation-compatibility
condition is hidden in this assertion. -/
theorem complexNormalTopLocalHomology_finrank (p : ℕ) :
    Module.finrank ℤ (LocalHomology.Cycles.localSingularHomology (TopCat.of (Fin p → ℂ)) 0 (2 * p)) = 1 := by
  simpa using (complexNormalTopLocalHomologyEquiv p).finrank_eq

/-- The explicit normal-coordinate comparison also proves vanishing away
from top degree, for local homology degrees at least two. -/
theorem positiveComplexNormalLocalHomology_isZero (p n : ℕ) (hn : n ≠ 0)
    (hnotTop : n + 1 ≠ 2 * p + 2) :
    IsZero (LocalHomology.Cycles.localSingularHomology (TopCat.of (Fin (p + 1) → ℂ)) 0 (n + 1)) :=
  (SphereHomologyInduction.Cycles.standardSphereHomology_isZero (2 * p + 1) n hn (by omega)).of_iso
    (positiveComplexNormalLocalStandardSphereIso p n hn)

end

end OAI.AlgebraicGeometry.CycleClass.Geometric.ComplexLocalTopHomology.Cycles

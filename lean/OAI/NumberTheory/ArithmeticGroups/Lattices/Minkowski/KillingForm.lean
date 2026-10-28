import OAI.NumberTheory.ArithmeticGroups.Lattices.Lie.OrderBases
import OAI.NumberTheory.ArithmeticGroups.Lattices.KillingRestriction
import OAI.NumberTheory.ArithmeticGroups.Lattices.SemilinearTrace

/-! # Killing Form -/

namespace OAI.NumberTheory.ArithmeticGroups.Lattices.Minkowski.KillingForm.Construction

noncomputable section

/-! The real Minkowski Lie bracket has a nondegenerate intrinsic
Killing form, obtained from the rational Killing form in integral bases. -/

open scoped Classical _root_.NumberField _root_.Matrix.Norms.Elementwise
open _root_.NumberField _root_.NumberField.mixedEmbedding _root_.Module

attribute [local instance] LieRing.ofAssociativeRing KillingRestriction.Construction.infinitesimalRationalLieAlgebra

def lieMixedKillingForm
    {k : Type} [Field k] [NumberField k] {n : ℕ}
    (G : Algebraic.MatrixAlgebraicGroup k n) (hG : G.IsGeometricallyConnected) :
    LinearMap.BilinForm ℝ (Lie.MixedLattice.Construction.lieMixedSpan G) :=
  ((LinearMap.mul ℝ (Module.End ℝ (Lie.MixedLattice.Construction.lieMixedSpan G))).compl₁₂
    (AdjointOperator.Construction.lieMixedAdjointLinear G hG) (AdjointOperator.Construction.lieMixedAdjointLinear G hG)).compr₂ (LinearMap.trace ℝ (Lie.MixedLattice.Construction.lieMixedSpan G))

def lieMixedRationalSemilinear
    {k : Type} [Field k] [NumberField k] {n : ℕ} (G : Algebraic.MatrixAlgebraicGroup k n) :
    Infinitesimal.Action.Construction.infinitesimalStabilizer G →ₛₗ[algebraMap ℚ ℝ] Lie.MixedLattice.Construction.lieMixedSpan G where
  toFun := Archimedean.Lie.Construction.lieMixedSpanRationalMap G
  map_add' := (Archimedean.Lie.Construction.lieMixedSpanRationalMap G).map_add
  map_smul' r A := by
    rw [(Archimedean.Lie.Construction.lieMixedSpanRationalMap G).map_smul]
    exact (IsScalarTower.algebraMap_smul ℝ r (Archimedean.Lie.Construction.lieMixedSpanRationalMap G A)).symm

theorem lieMixedKillingForm_rational
    {k ι : Type} [Field k] [NumberField k] [Fintype ι] [DecidableEq ι] {n : ℕ}
    (G : Algebraic.MatrixAlgebraicGroup k n) (hG : G.IsGeometricallyConnected)
    (b : Basis ι ℤ (Integral.Lie.Construction.integralLieOrder G)) (A B : Infinitesimal.Action.Construction.infinitesimalStabilizer G) :
    lieMixedKillingForm G hG (Archimedean.Lie.Construction.lieMixedSpanRationalMap G A) (Archimedean.Lie.Construction.lieMixedSpanRationalMap G B) =
      algebraMap ℚ ℝ (killingForm ℚ (Infinitesimal.Action.Construction.infinitesimalStabilizer G) A B) := by
  symm
  apply SemilinearTrace.Construction.semilinear_intertwining_trace (algebraMap ℚ ℝ) (Lie.OrderBases.Construction.lieOrderRationalBasis G b) (Lie.OrderBases.Construction.lieOrderRealBasis G b)
    (lieMixedRationalSemilinear G) (fun i => (Lie.OrderBases.Construction.lieOrderRealBasis_apply G b i).symm)
    ((LieAlgebra.ad ℚ (Infinitesimal.Action.Construction.infinitesimalStabilizer G) A).comp (LieAlgebra.ad ℚ (Infinitesimal.Action.Construction.infinitesimalStabilizer G) B))
    (AdjointOperator.Construction.lieMixedAdjoint G hG (Archimedean.Lie.Construction.lieMixedSpanRationalMap G A) * AdjointOperator.Construction.lieMixedAdjoint G hG (Archimedean.Lie.Construction.lieMixedSpanRationalMap G B))
  intro X
  change Archimedean.Lie.Construction.lieMixedSpanRationalMap G (LieAlgebra.ad k (Infinitesimal.Action.Construction.infinitesimalStabilizer G) A
      (LieAlgebra.ad k (Infinitesimal.Action.Construction.infinitesimalStabilizer G) B X)) =
    AdjointOperator.Construction.lieMixedAdjoint G hG (Archimedean.Lie.Construction.lieMixedSpanRationalMap G A)
      (AdjointOperator.Construction.lieMixedAdjoint G hG (Archimedean.Lie.Construction.lieMixedSpanRationalMap G B) (Archimedean.Lie.Construction.lieMixedSpanRationalMap G X))
  rw [AdjointOperator.Construction.lieMixedAdjoint_rational, AdjointOperator.Construction.lieMixedAdjoint_rational]

theorem lieMixedKillingForm_nondegenerate
    {k : Type} [Field k] [NumberField k] {n : ℕ}
    (G : Algebraic.MatrixAlgebraicGroup k n) (hG : G.IsGeometricallyConnected) (hsemi : G.IsSemisimple) :
    (lieMixedKillingForm G hG).Nondegenerate := by
  let : Module.Free ℤ (Integral.Lie.Construction.integralLieOrder G) := Lie.MixedLattice.Construction.integralLieOrder_free G
  let : Module.Finite ℤ (Integral.Lie.Construction.integralLieOrder G) := Integral.Lie.Construction.integralLieOrder_finite G
  let b := Module.finBasis ℤ (Integral.Lie.Construction.integralLieOrder G)
  let bQ := Lie.OrderBases.Construction.lieOrderRationalBasis G b
  let bR := Lie.OrderBases.Construction.lieOrderRealBasis G b
  let : LieAlgebra.IsKilling ℚ (Infinitesimal.Action.Construction.infinitesimalStabilizer G) := KillingRestriction.Construction.infinitesimal_rational_isKilling G hG hsemi
  have he : LinearMap.BilinForm.toMatrix bR (lieMixedKillingForm G hG) =
      (LinearMap.BilinForm.toMatrix bQ (killingForm ℚ (Infinitesimal.Action.Construction.infinitesimalStabilizer G))).map (algebraMap ℚ ℝ) := by
    ext i j : 1
    rw [LinearMap.BilinForm.toMatrix_apply, Matrix.map_apply, LinearMap.BilinForm.toMatrix_apply]
    change lieMixedKillingForm G hG (Lie.OrderBases.Construction.lieOrderRealBasis G b i) (Lie.OrderBases.Construction.lieOrderRealBasis G b j) = _
    rw [Lie.OrderBases.Construction.lieOrderRealBasis_apply, Lie.OrderBases.Construction.lieOrderRealBasis_apply]
    exact lieMixedKillingForm_rational G hG b _ _
  rw [LinearMap.BilinForm.nondegenerate_iff_det_ne_zero bR, he]
  change ((algebraMap ℚ ℝ).mapMatrix
    (LinearMap.BilinForm.toMatrix bQ (killingForm ℚ (Infinitesimal.Action.Construction.infinitesimalStabilizer G)))).det ≠ 0
  rw [← RingHom.map_det]
  exact (map_ne_zero (algebraMap ℚ ℝ)).mpr
    ((LinearMap.BilinForm.nondegenerate_iff_det_ne_zero bQ).mp
      (LieAlgebra.IsKilling.killingForm_nondegenerate ℚ (Infinitesimal.Action.Construction.infinitesimalStabilizer G)))

end

end OAI.NumberTheory.ArithmeticGroups.Lattices.Minkowski.KillingForm.Construction

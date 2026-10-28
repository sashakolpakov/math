import OAI.AlgebraicGeometry.CycleClass.Thom.ResidueDegree
import OAI.AlgebraicGeometry.Divisors.LineBundles.Ord
import Mathlib.LinearAlgebra.Dimension.Free

/-! # Point -/

namespace OAI.AlgebraicGeometry.CycleClass.Thom.Point.Constructions

noncomputable section

/-!
# ThomClass: proper cycle pushforward in generic-point coordinates

The weights in the constructed pushforward are degrees of the actual residue
field extensions. Their tower law makes ungraded pushforward functorial. The
comparison with the graded cycle construction keeps all multiplicities.
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace
open scoped Classical

open OAI.AlgebraicGeometry.CycleClass.Thom.ResidueDegree.Constructions

/-- Finite cycle pushforward in native generic-point coordinates. -/
def pointPushforward {X Y : Scheme} (f : X ⟶ Y) : (X →₀ ℚ) →ₗ[ℚ] (Y →₀ ℚ) :=
  Finsupp.linearCombination ℚ
    (fun x => Finsupp.single (f x) (f.residueDegree x : ℚ))

theorem pointPushforward_single {X Y : Scheme} (f : X ⟶ Y) (x : X) (a : ℚ) :
    pointPushforward f (Finsupp.single x a) =
      Finsupp.single (f x) (a * (f.residueDegree x : ℚ)) := by
  rw [pointPushforward, Finsupp.linearCombination_single, Finsupp.smul_single]
  rfl

theorem pointPushforward_id (X : Scheme) : pointPushforward (𝟙 X) = LinearMap.id := by
  apply Finsupp.lhom_ext
  intro x a
  rw [pointPushforward_single, Scheme.Hom.residueDegree_id]
  simp only [Nat.cast_one, mul_one, LinearMap.id_apply]
  rfl

theorem pointPushforward_comp {X Y Z : Scheme} (f : X ⟶ Y) (g : Y ⟶ Z) :
    pointPushforward (f ≫ g) = (pointPushforward g).comp (pointPushforward f) := by
  apply Finsupp.lhom_ext
  intro x a
  rw [LinearMap.comp_apply, pointPushforward_single, pointPushforward_single,
    pointPushforward_single, ResidueDegree.Constructions.residueDegree_comp, Nat.cast_mul]
  congr 1
  ring

/-- The same finite principal divisor with rational coefficients. -/
def rationalPrincipalPointDivisor (A : Scheme) [IsIntegral A]
    [AlgebraicGeometry.IsNoetherian A] (f : A.functionField) : A →₀ ℚ :=
  (Divisors.LineBundles.Ord.BundleCycles.principalDivisor A f).mapRange (fun n : ℤ => (n : ℚ)) Int.cast_zero

@[simp]
theorem rationalPrincipalPointDivisor_apply (A : Scheme) [IsIntegral A]
    [AlgebraicGeometry.IsNoetherian A] (f : A.functionField) (x : A) :
    rationalPrincipalPointDivisor A f x = (A.ord f x : ℚ) := rfl

end

end OAI.AlgebraicGeometry.CycleClass.Thom.Point.Constructions

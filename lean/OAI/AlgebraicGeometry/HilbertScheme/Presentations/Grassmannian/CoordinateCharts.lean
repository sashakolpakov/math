import Mathlib.RingTheory.Grassmannian
import Mathlib.LinearAlgebra.Prod

/-! # Coordinate Charts -/

namespace OAI.AlgebraicGeometry.HilbertScheme.Presentations.Grassmannian.CoordinateCharts

noncomputable section

/-!
Coordinate charts for the finite free Grassmannian, as used in the relative
Hilbert construction. The chart condition says that the first coordinate
summand maps isomorphically onto the actual quotient module.
-/

universe u v w

variable {R : Type u} [CommRing R]
variable {V : Type v} [AddCommGroup V] [Module R V]
variable {W : Type w} [AddCommGroup W] [Module R W]

/-- The quotient map in the chart with the first summand as quotient basis. -/
def chartQuotientMap (L : W →ₗ[R] V) : V × W →ₗ[R] V :=
  LinearMap.fst R V W + L.comp (LinearMap.snd R V W)

@[simp] theorem chartQuotientMap_apply (L : W →ₗ[R] V) (x : V × W) :
    chartQuotientMap L x = x.1 + L x.2 := rfl

theorem chartQuotientMap_surjective (L : W →ₗ[R] V) :
    Function.Surjective (chartQuotientMap L) := by
  intro x
  exact ⟨(x, 0), by simp⟩

/-- The actual kernel submodule represented by the chart coordinate L. -/
def chartKernel (L : W →ₗ[R] V) : Submodule R (V × W) :=
  (chartQuotientMap L).ker

def chartQuotientEquiv (L : W →ₗ[R] V) :
    ((V × W) ⧸ chartKernel L) ≃ₗ[R] V :=
  (chartQuotientMap L).quotKerEquivOfSurjective (chartQuotientMap_surjective L)

@[simp] theorem chartQuotientEquiv_mk (L : W →ₗ[R] V) (x : V × W) :
    chartQuotientEquiv L ((chartKernel L).mkQ x) = x.1 + L x.2 :=
  LinearMap.quotKerEquivOfSurjective_apply_mk _ _ _

/-- Restriction of the quotient projection to the first summand. -/
def quotientLeft (N : Submodule R (V × W)) : V →ₗ[R] ((V × W) ⧸ N) :=
  N.mkQ.comp (LinearMap.inl R V W)

/-- The standard chart consists of submodules with this restriction invertible. -/
def Chart (R : Type u) [CommRing R]
    (V : Type v) [AddCommGroup V] [Module R V]
    (W : Type w) [AddCommGroup W] [Module R W] :=
  {N : Submodule R (V × W) // Function.Bijective (quotientLeft N)}

theorem chartKernel_in_chart (L : W →ₗ[R] V) :
    Function.Bijective (quotientLeft (chartKernel L)) := by
  have h (x : V) : chartQuotientEquiv L (quotientLeft (chartKernel L) x) = x := by
    change chartQuotientEquiv L ((chartKernel L).mkQ (x, 0)) = x
    rw [chartQuotientEquiv_mk, map_zero, add_zero]
  constructor
  · intro x y hxy
    simpa only [h] using congrArg (chartQuotientEquiv L) hxy
  · intro z
    refine ⟨chartQuotientEquiv L z, (chartQuotientEquiv L).injective ?_⟩
    exact h _

def chartOfMap (L : W →ₗ[R] V) : Chart R V W :=
  ⟨chartKernel L, chartKernel_in_chart L⟩

/-- Quotient coordinates are canonically fixed by the first summand. -/
def leftQuotientEquiv (N : Chart R V W) : V ≃ₗ[R] ((V × W) ⧸ N.val) :=
  LinearEquiv.ofBijective (quotientLeft N.val) N.property

/-- The remaining columns of the quotient map are the affine coordinates. -/
def chartCoordinate (N : Chart R V W) : W →ₗ[R] V :=
  (leftQuotientEquiv N).symm.toLinearMap.comp
    (N.val.mkQ.comp (LinearMap.inr R V W))

theorem quotient_coordinate_formula (N : Chart R V W) (x : V × W) :
    (leftQuotientEquiv N).symm (N.val.mkQ x) =
      x.1 + chartCoordinate N x.2 := by
  have hx : x = (x.1, 0) + (0, x.2) := by simp
  calc
    _ = (leftQuotientEquiv N).symm
        (N.val.mkQ (x.1, 0) + N.val.mkQ (0, x.2)) := by
      rw [← map_add, ← hx]
    _ = (leftQuotientEquiv N).symm (N.val.mkQ (x.1, 0)) +
        (leftQuotientEquiv N).symm (N.val.mkQ (0, x.2)) := map_add _ _ _
    _ = x.1 + chartCoordinate N x.2 := by
      change (leftQuotientEquiv N).symm (leftQuotientEquiv N x.1) +
        chartCoordinate N x.2 = _
      rw [LinearEquiv.symm_apply_apply]

theorem chartKernel_chartCoordinate (N : Chart R V W) :
    chartKernel (chartCoordinate N) = N.val := by
  ext x
  change x.1 + chartCoordinate N x.2 = 0 ↔ x ∈ N.val
  rw [← quotient_coordinate_formula N x, LinearEquiv.map_eq_zero_iff]
  exact Submodule.Quotient.mk_eq_zero N.val

theorem chartKernel_injective : Function.Injective (chartKernel (R := R) (V := V) (W := W)) := by
  intro L K h
  ext y
  have hy : (-L y, y) ∈ chartKernel L := by
    change -L y + L y = 0
    exact neg_add_cancel _
  rw [h] at hy
  change -L y + K y = 0 at hy
  exact eq_of_neg_add_eq_zero hy

/-- Every standard Grassmannian chart is the full affine space of matrices. -/
def chartEquiv : (W →ₗ[R] V) ≃ Chart R V W where
  toFun := chartOfMap
  invFun := chartCoordinate
  left_inv L := chartKernel_injective (chartKernel_chartCoordinate (chartOfMap L))
  right_inv N := Subtype.ext (chartKernel_chartCoordinate N)

/-- The quotients parametrized by a chart really are finite projective modules
of the prescribed constant rank, including over non-field base rings. -/
def chartGrassmannian (k m : ℕ) (L : (Fin m → R) →ₗ[R] (Fin k → R)) :
    Module.Grassmannian R ((Fin k → R) × (Fin m → R)) k where
  toSubmodule := chartKernel L
  finite_quotient := Module.Finite.equiv (chartQuotientEquiv L).symm
  projective_quotient := Module.Projective.of_equiv (chartQuotientEquiv L).symm
  rankAtStalk_eq p := by
    have : Nontrivial R := Function.Surjective.nontrivial
      (f := Ideal.Quotient.mk p.asIdeal) Ideal.Quotient.mk_surjective
    rw [congrFun (Module.rankAtStalk_eq_of_equiv (chartQuotientEquiv L)) p]
    rw [Module.rankAtStalk_eq_finrank_of_free]
    simp

end

end OAI.AlgebraicGeometry.HilbertScheme.Presentations.Grassmannian.CoordinateCharts

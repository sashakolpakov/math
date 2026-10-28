import OAI.ArithmeticGeometry.Descent.CMVariety.IntegralMarkedMaps
import OAI.ArithmeticGeometry.Descent.CMVariety.MarkedActions
import Mathlib.Analysis.Calculus.ContDiff.Operations

/-! # Period Coordinate Continuity -/

namespace OAI.ArithmeticGeometry.Descent.CMVariety.PeriodCoordinateContinuity.Abelian.IntrinsicPeriods

noncomputable section

section

/-!
Real coordinates of the actual integral period lattice. The marked
endomorphism matrix is recovered by taking real period coordinates of
the native linear lift on each lattice basis vector. Continuous period
vectors and continuous images therefore give continuous marked matrices.
-/

open _root_.CategoryTheory
open OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.AbelianUniformizationEq.Constructions.AbelianUniformization
open scoped _root_.Topology BigOperators

variable {Index : Type} [Fintype Index]

local instance (A : AlgebraicGeometry.ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety) : IsZLattice ℝ (AlgebraicGeometry.HodgeConjecture.DegreeTwo.AbelianUniformizationEq.Constructions.AbelianUniformization.periodLattice A) :=
  AlgebraicGeometry.HodgeConjecture.DegreeTwo.AbelianUniformizationEq.Constructions.AbelianUniformization.periodLattice_full IntrinsicHodgeMaps.Abelian.IntrinsicPeriods.algebraization A

/-- A marking of the actual full integral lattice is a real basis of
the native tangent space. -/
def realPeriodEquiv {A : AlgebraicGeometry.ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety} (b : MarkedAbelianPeriods.IntrinsicPeriods.Marking Index A) :
    (Index → ℝ) ≃L[ℝ] AlgebraicGeometry.HodgeConjecture.DegreeTwo.Transport.Constructions.AbelianModel A :=
  (b.ofZLatticeBasis ℝ (AlgebraicGeometry.HodgeConjecture.DegreeTwo.AbelianUniformizationEq.Constructions.AbelianUniformization.periodLattice A)).equivFun.symm.toContinuousLinearEquiv

theorem realPeriodEquiv_symm_lattice {A : AlgebraicGeometry.ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety}
    (b : MarkedAbelianPeriods.IntrinsicPeriods.Marking Index A) (l : AlgebraicGeometry.HodgeConjecture.DegreeTwo.AbelianUniformizationEq.Constructions.AbelianUniformization.periodLattice A) (i : Index) :
    (realPeriodEquiv b).symm (l : AlgebraicGeometry.HodgeConjecture.DegreeTwo.Transport.Constructions.AbelianModel A) i = (b.repr l i : ℝ) :=
  b.ofZLatticeBasis_repr_apply ℝ (AlgebraicGeometry.HodgeConjecture.DegreeTwo.AbelianUniformizationEq.Constructions.AbelianUniformization.periodLattice A) l i

theorem realPeriodEquiv_basis {A : AlgebraicGeometry.ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety} (b : MarkedAbelianPeriods.IntrinsicPeriods.Marking Index A) (i : Index) :
    realPeriodEquiv b ((Pi.basisFun ℝ Index) i) = (b i : AlgebraicGeometry.HodgeConjecture.DegreeTwo.Transport.Constructions.AbelianModel A) := by
  classical
  change (b.ofZLatticeBasis ℝ (AlgebraicGeometry.HodgeConjecture.DegreeTwo.AbelianUniformizationEq.Constructions.AbelianUniformization.periodLattice A)).equivFun.symm
    ((Pi.basisFun ℝ Index) i) = _
  erw [Module.Basis.equivFun_symm_apply]
  simp [Pi.basisFun_apply]
  exact b.ofZLatticeBasis_apply ℝ (AlgebraicGeometry.HodgeConjecture.DegreeTwo.AbelianUniformizationEq.Constructions.AbelianUniformization.periodLattice A) i

/-- The real coordinate inverse recovers the integral transpose entry. -/
theorem markedEndomorphism_real_entry {A : AlgebraicGeometry.ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety}
    (b : MarkedAbelianPeriods.IntrinsicPeriods.Marking Index A) (f : A.toOver ⟶ A.toOver) [IsMonHom f] (i j : Index) :
    (MarkedActions.Abelian.IntrinsicPeriods.markedEndomorphism b f ((Pi.basisFun ℚ Index) i) j : ℝ) =
      (realPeriodEquiv b).symm (IntegralMarkedMaps.Abelian.IntrinsicPeriods.algebraicLinearLift f (b j : AlgebraicGeometry.HodgeConjecture.DegreeTwo.Transport.Constructions.AbelianModel A)) i := by
  rw [IntegralMarkedMaps.Abelian.IntrinsicPeriods.markedEndomorphism_integer_entry, Rat.cast_intCast]
  exact (realPeriodEquiv_symm_lattice b (IntegralMarkedMaps.Abelian.IntrinsicPeriods.algebraicLatticeMap f (b j)) i).symm

/-- Inverses of a continuously varying real period basis are continuous,
including their evaluation on a varying vector. -/
theorem continuousAt_equiv_symm_apply
    {S E F : Type*} [TopologicalSpace S]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (e : S → E ≃L[ℝ] F) (v : S → F) (s₀ : S)
    (he : ContinuousAt (fun s => (e s).toContinuousLinearMap) s₀)
    (hv : ContinuousAt v s₀) : ContinuousAt (fun s => (e s).symm (v s)) s₀ := by
  have hinv : ContinuousAt
      (ContinuousLinearMap.inverse : (E →L[ℝ] F) → (F →L[ℝ] E))
      (e s₀).toContinuousLinearMap :=
    (contDiffAt_map_inverse (n := 0) (e s₀)).continuousAt
  have hi : ContinuousAt (fun s => (e s).toContinuousLinearMap.inverse) s₀ :=
    ContinuousAt.comp (f := fun s => (e s).toContinuousLinearMap) (x := s₀) hinv he
  have h := hi.clm_apply hv
  simpa only [ContinuousLinearMap.inverse_equiv, ContinuousLinearEquiv.coe_coe] using h

/-- Tangent coordinates of the real period basis. -/
def realPeriodInCoordinates {A : AlgebraicGeometry.ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety} {d : ℕ}
    (b : MarkedAbelianPeriods.IntrinsicPeriods.Marking Index A) (e : AlgebraicGeometry.HodgeConjecture.DegreeTwo.Transport.Constructions.AbelianModel A ≃ₗ[ℂ] (Fin d → ℂ)) :
    (Index → ℝ) ≃L[ℝ] (Fin d → ℂ) :=
  (realPeriodEquiv b).trans (e.restrictScalars ℝ).toContinuousLinearEquiv

/-- Continuity of the real period basis and the native lifted images
implies continuity of the actual marked cohomology matrices. -/
theorem markedEndomorphism_continuous_of_lift_images
    {S : Type} [TopologicalSpace S]
    (A : S → AlgebraicGeometry.ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety) (b : ∀ s, MarkedAbelianPeriods.IntrinsicPeriods.Marking Index (A s))
    (d : ℕ) (e : ∀ s, AlgebraicGeometry.HodgeConjecture.DegreeTwo.Transport.Constructions.AbelianModel (A s) ≃ₗ[ℂ] (Fin d → ℂ))
    (f : ∀ s, (A s).toOver ⟶ (A s).toOver) (hf : ∀ s, IsMonHom (f s))
    (s₀ : S)
    (hperiod : ContinuousAt
      (fun s => (realPeriodInCoordinates (b s) (e s)).toContinuousLinearMap) s₀)
    (himages : let (s : S) : IsMonHom (f s) := hf s
      ∀ j, ContinuousAt
        (fun s => e s (IntegralMarkedMaps.Abelian.IntrinsicPeriods.algebraicLinearLift (f s) (b s j : AlgebraicGeometry.HodgeConjecture.DegreeTwo.Transport.Constructions.AbelianModel (A s)))) s₀) :
    ∀ i j, ContinuousAt
      (fun s => (MarkedActions.Abelian.IntrinsicPeriods.markedEndomorphism (b s) (f s) ((Pi.basisFun ℚ Index) i) j : ℝ)) s₀ := by
  let (s : S) : IsMonHom (f s) := hf s
  intro i j
  have h := continuousAt_equiv_symm_apply
    (fun s => realPeriodInCoordinates (b s) (e s))
    (fun s => e s (IntegralMarkedMaps.Abelian.IntrinsicPeriods.algebraicLinearLift (f s) (b s j : AlgebraicGeometry.HodgeConjecture.DegreeTwo.Transport.Constructions.AbelianModel (A s))))
    s₀ hperiod (himages j)
  have hi := (continuous_apply i).continuousAt.comp h
  convert hi using 1
  ext s
  rw [markedEndomorphism_real_entry]
  change (realPeriodEquiv (b s)).symm _ i =
    (realPeriodEquiv (b s)).symm ((e s).symm ((e s) _)) i
  rw [LinearEquiv.symm_apply_apply]

end

/-!
The real period basis varies continuously when the complex marked period
matrix does. Together with the previous native-lift comparison, this
reduces continuity of marked endomorphism matrices to continuity of the
lifted images of the actual marked lattice vectors.
-/

open _root_.CategoryTheory
open scoped _root_.Topology

variable {Index : Type} [Fintype Index]

/-- Continuity of the finitely many marked vectors proves continuity of
the full complex period matrix in fixed tangent coordinates. -/
theorem continuousAt_period_map_of_vectors
    {S : Type} [TopologicalSpace S]
    (A : S → AlgebraicGeometry.ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety) (b : ∀ s, MarkedAbelianPeriods.IntrinsicPeriods.Marking Index (A s))
    (d : ℕ) (e : ∀ s, AlgebraicGeometry.HodgeConjecture.DegreeTwo.Transport.Constructions.AbelianModel (A s) ≃ₗ[ℂ] (Fin d → ℂ))
    (s₀ : S) (hv : ∀ i, ContinuousAt (fun s => e s (b s i : AlgebraicGeometry.HodgeConjecture.DegreeTwo.Transport.Constructions.AbelianModel (A s))) s₀) :
    ContinuousAt
      (fun s => ((e s).toLinearMap.comp (MarkedAbelianPeriods.IntrinsicPeriods.periodMap (b s))).toContinuousLinearMap) s₀ := by
  classical
  let frames := ContinuousLinearEquiv.piRing (𝕜 := ℂ) (E := Fin d → ℂ) Index
  have h : ContinuousAt (fun s => frames.symm (fun i => e s (b s i : AlgebraicGeometry.HodgeConjecture.DegreeTwo.Transport.Constructions.AbelianModel (A s)))) s₀ :=
    frames.symm.continuous.continuousAt.comp (continuousAt_pi.mpr hv)
  have heq (s : S) : frames.symm (fun i => e s (b s i : AlgebraicGeometry.HodgeConjecture.DegreeTwo.Transport.Constructions.AbelianModel (A s))) =
      ((e s).toLinearMap.comp (MarkedAbelianPeriods.IntrinsicPeriods.periodMap (b s))).toContinuousLinearMap := by
    apply frames.injective
    rw [ContinuousLinearEquiv.apply_symm_apply]
    funext i
    change e s (b s i : AlgebraicGeometry.HodgeConjecture.DegreeTwo.Transport.Constructions.AbelianModel (A s)) = e s (MarkedAbelianPeriods.IntrinsicPeriods.periodMap (b s) (Pi.single i 1))
    congr 1
    exact ((Pi.basisFun ℂ Index).constr_basis ℂ (fun j => (b s j : AlgebraicGeometry.HodgeConjecture.DegreeTwo.Transport.Constructions.AbelianModel (A s))) i).symm
  simpa only [heq] using h

def realToComplexCoordinates : (Index → ℝ) →L[ℝ] (Index → ℂ) :=
  (show (Index → ℝ) →ₗ[ℝ] (Index → ℂ) from
    { toFun v := fun i => (v i : ℂ)
      map_add' v w := by ext i; simp
      map_smul' c v := by ext i; simp }).toContinuousLinearMap

theorem realToComplexCoordinates_basis (i : Index) :
    realToComplexCoordinates ((Pi.basisFun ℝ Index) i) = (Pi.basisFun ℂ Index) i := by
  classical
  ext j
  change (((Pi.basisFun ℝ Index) i j : ℝ) : ℂ) = (Pi.basisFun ℂ Index) i j
  by_cases h : i = j <;> simp [Pi.basisFun_apply, h]

theorem realPeriodInCoordinates_eq_restriction {A : AlgebraicGeometry.ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety} {d : ℕ}
    (b : MarkedAbelianPeriods.IntrinsicPeriods.Marking Index A) (e : AlgebraicGeometry.HodgeConjecture.DegreeTwo.Transport.Constructions.AbelianModel A ≃ₗ[ℂ] (Fin d → ℂ)) :
    (realPeriodInCoordinates b e).toContinuousLinearMap =
      ((e.toLinearMap.comp (MarkedAbelianPeriods.IntrinsicPeriods.periodMap b)).toContinuousLinearMap.restrictScalars ℝ).comp
        realToComplexCoordinates := by
  suffices h : (realPeriodInCoordinates b e).toContinuousLinearMap.toLinearMap =
      (((e.toLinearMap.comp (MarkedAbelianPeriods.IntrinsicPeriods.periodMap b)).toContinuousLinearMap.restrictScalars ℝ).comp
        realToComplexCoordinates).toLinearMap from
    DFunLike.ext _ _ (LinearMap.congr_fun h)
  apply (Pi.basisFun ℝ Index).ext
  intro i
  change e (realPeriodEquiv b ((Pi.basisFun ℝ Index) i)) =
    e (MarkedAbelianPeriods.IntrinsicPeriods.periodMap b (realToComplexCoordinates ((Pi.basisFun ℝ Index) i)))
  rw [realPeriodEquiv_basis, realToComplexCoordinates_basis]
  congr 1
  exact ((Pi.basisFun ℂ Index).constr_basis ℂ (fun j => (b j : AlgebraicGeometry.HodgeConjecture.DegreeTwo.Transport.Constructions.AbelianModel A)) i).symm

theorem realPeriodInCoordinates_continuousAt
    {S : Type} [TopologicalSpace S]
    (A : S → AlgebraicGeometry.ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety) (b : ∀ s, MarkedAbelianPeriods.IntrinsicPeriods.Marking Index (A s))
    (d : ℕ) (e : ∀ s, AlgebraicGeometry.HodgeConjecture.DegreeTwo.Transport.Constructions.AbelianModel (A s) ≃ₗ[ℂ] (Fin d → ℂ))
    (s₀ : S)
    (hp : ContinuousAt
      (fun s => ((e s).toLinearMap.comp (MarkedAbelianPeriods.IntrinsicPeriods.periodMap (b s))).toContinuousLinearMap) s₀) :
    ContinuousAt
      (fun s => (realPeriodInCoordinates (b s) (e s)).toContinuousLinearMap) s₀ := by
  have hr : ContinuousAt
      (fun s => ((e s).toLinearMap.comp (MarkedAbelianPeriods.IntrinsicPeriods.periodMap (b s))).toContinuousLinearMap.restrictScalars ℝ)
      s₀ :=
    (ContinuousLinearMap.restrictScalarsIsometry ℂ (Index → ℂ) (Fin d → ℂ) ℝ ℝ).continuous.continuousAt.comp hp
  have h := hr.clm_comp (continuousAt_const (y := realToComplexCoordinates (Index := Index)))
  simpa only [realPeriodInCoordinates_eq_restriction] using h

end

end OAI.ArithmeticGeometry.Descent.CMVariety.PeriodCoordinateContinuity.Abelian.IntrinsicPeriods

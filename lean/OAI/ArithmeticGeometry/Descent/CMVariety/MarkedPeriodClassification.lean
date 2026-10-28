import OAI.ArithmeticGeometry.Descent.CMVariety.MarkedAbelianPeriods
import Mathlib.LinearAlgebra.TensorProduct.Basis

/-! # Marked Period Classification -/

namespace OAI.ArithmeticGeometry.Descent.CMVariety.MarkedPeriodClassification.Abelian.IntrinsicPeriods

noncomputable section

section

/-!
The marked Betti coordinates descend to the actual rational H¹. Their
scalar extension agrees with the integration-normalized complex marking.
This connects the rational CM action to the native marked period chart.
-/

open OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.AbelianUniformizationEq.Constructions.AbelianUniformization
open OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.AbelianPeriodsTo.Constructions.AbelianPeriods OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.AbelianComparison.Constructions
open OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.LatticePeriod.Constructions.LatticeDual
open scoped TensorProduct

variable {ι : Type} [Fintype ι]

/-- Rational Betti coordinates obtained by evaluation on the same marked lattice. -/
def rationalCoordinates {A : AlgebraicGeometry.ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety} (b : MarkedAbelianPeriods.IntrinsicPeriods.Marking ι A) :
    A.variety.rationalCohomology 1 ≃ₗ[ℚ] (ι → ℚ) :=
  (AlgebraicGeometry.HodgeConjecture.DegreeTwo.AbelianComparison.Constructions.rationalH1Equiv IntrinsicHodgeMaps.Abelian.IntrinsicPeriods.algebraization A).trans
    ((AlgebraicGeometry.HodgeConjecture.DegreeTwo.LatticePeriod.Constructions.LatticeDual.characterRestrictionEquiv (K := ℚ) (AlgebraicGeometry.HodgeConjecture.DegreeTwo.AbelianUniformizationEq.Constructions.AbelianUniformization.periodLattice A)).trans
      ((addMonoidHomLequivInt ℚ).trans (b.constr ℚ).symm))

omit [Fintype ι] in
theorem rationalCoordinates_apply {A : AlgebraicGeometry.ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety} (b : MarkedAbelianPeriods.IntrinsicPeriods.Marking ι A)
    (x : A.variety.rationalCohomology 1) (i : ι) :
    rationalCoordinates b x i =
      AlgebraicGeometry.HodgeConjecture.DegreeTwo.AbelianComparison.Constructions.rationalH1Equiv IntrinsicHodgeMaps.Abelian.IntrinsicPeriods.algebraization A x (AlgebraicGeometry.HodgeConjecture.DegreeTwo.LatticePeriod.Constructions.LatticeDual.latticeInclusion (AlgebraicGeometry.HodgeConjecture.DegreeTwo.AbelianUniformizationEq.Constructions.AbelianUniformization.periodLattice A) (b i)) := rfl

/-- Coordinates on the actual scalar extension of the rational marking space. -/
def scalarCoordinates : AlgebraicGeometry.ComplexMultiplication.WeightOne.CM.Complexification (ι → ℚ) ≃ₗ[ℂ] (ι → ℂ) :=
  ((Pi.basisFun ℚ ι).baseChange ℂ).equivFun

theorem scalarCoordinates_tmul (z : ℂ) (v : ι → ℚ) (i : ι) :
    scalarCoordinates (z ⊗ₜ[ℚ] v) i = z * (v i : ℂ) := by
  simp [scalarCoordinates, Module.Basis.equivFun_apply, Module.Basis.baseChange_repr_tmul,
    Rat.smul_def, mul_comm]

omit [Fintype ι] in
theorem complexCoordinates_rationalToComplex {A : AlgebraicGeometry.ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety} (b : MarkedAbelianPeriods.IntrinsicPeriods.Marking ι A)
    (x : A.variety.rationalCohomology 1) (i : ι) :
    MarkedAbelianPeriods.IntrinsicPeriods.complexCoordinates b (AlgebraicTopology.Cohomology.Singular.RationalComplex.rationalToComplexCohomology (AlgebraicGeometry.Betti.Scheme.schemePointSpace A.toOver) 1 x) i =
      (rationalCoordinates b x i : ℂ) := by
  erw [MarkedAbelianPeriods.IntrinsicPeriods.complexCoordinates_apply, rationalCoordinates_apply]
  exact AlgebraicGeometry.HodgeConjecture.DegreeTwo.AbelianPeriodsTo.Constructions.AbelianPeriods.complexPeriods_rationalToComplex IntrinsicHodgeMaps.Abelian.IntrinsicPeriods.algebraization A x (b i)

/-- The complex marking is exactly the scalar extension of the rational
one under the canonical singular-cohomology coefficient comparison. -/
theorem complexCoordinates_baseChange {A : AlgebraicGeometry.ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety} (b : MarkedAbelianPeriods.IntrinsicPeriods.Marking ι A)
    (H : AlgebraicGeometry.ComplexMultiplication.WeightOne.CM.WeightOneHodgeStructure (A.variety.rationalCohomology 1))
    (x : AlgebraicGeometry.ComplexMultiplication.WeightOne.CM.Complexification (A.variety.rationalCohomology 1)) :
    MarkedAbelianPeriods.IntrinsicPeriods.complexCoordinates b (AlgebraicGeometry.HodgeConjecture.DegreeTwo.Transport.Constructions.h1ComplexificationEquiv A.variety H x) =
      scalarCoordinates ((rationalCoordinates b).toLinearMap.baseChange ℂ x) := by
  induction x using TensorProduct.inductionOn with
  | add x y hx hy => simp only [map_add, hx, hy]
  | tmul z x =>
    ext i
    change MarkedAbelianPeriods.IntrinsicPeriods.complexCoordinates b (AlgebraicGeometry.ComplexMultiplication.CohomologyBaseChange.CM.singularCohomologyComplexification
        (AlgebraicGeometry.Betti.Scheme.schemePointSpace A.toOver) 1 (z ⊗ₜ[ℚ] x)) i = _
    rw [AlgebraicGeometry.ComplexMultiplication.CohomologyBaseChange.CM.singularCohomologyComplexification_tmul]
    erw [(MarkedAbelianPeriods.IntrinsicPeriods.complexCoordinates b).map_smul, Pi.smul_apply, smul_eq_mul, complexCoordinates_rationalToComplex,
      LinearMap.baseChange_tmul, scalarCoordinates_tmul]
    rfl

/-- The canonical Hodge structure in the fixed rational marking space. -/
def markedHodgeStructure {A : AlgebraicGeometry.ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety} (b : MarkedAbelianPeriods.IntrinsicPeriods.Marking ι A)
    (H : AlgebraicGeometry.ComplexMultiplication.WeightOne.CM.WeightOneHodgeStructure (A.variety.rationalCohomology 1)) :
    AlgebraicGeometry.ComplexMultiplication.WeightOne.CM.WeightOneHodgeStructure (ι → ℚ) := AlgebraicGeometry.HodgeConjecture.DegreeTwo.Transport.Constructions.hodgeAlongEquiv H (rationalCoordinates b).symm

/-- The scalar marking followed by the standard covector identification. -/
def scalarMarkedBetti : AlgebraicGeometry.ComplexMultiplication.WeightOne.CM.Complexification (ι → ℚ) ≃ₗ[ℂ] Module.Dual ℂ (ι → ℂ) :=
  scalarCoordinates.trans ((Pi.basisFun ℂ ι).constr ℂ)

omit [Fintype ι] in
theorem rationalCoordinates_baseChange_symm {A : AlgebraicGeometry.ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety} (b : MarkedAbelianPeriods.IntrinsicPeriods.Marking ι A)
    (x : AlgebraicGeometry.ComplexMultiplication.WeightOne.CM.Complexification (ι → ℚ)) :
    (rationalCoordinates b).toLinearMap.baseChange ℂ
      ((rationalCoordinates b).symm.toLinearMap.baseChange ℂ x) = x := by
  induction x using TensorProduct.inductionOn with
  | tmul z x =>
    simp only [LinearMap.baseChange_tmul, LinearEquiv.coe_coe, LinearEquiv.apply_symm_apply]
  | add x y hx hy => simp only [map_add, hx, hy]

theorem markedBetti_symm_baseChange {A : AlgebraicGeometry.ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety} (b : MarkedAbelianPeriods.IntrinsicPeriods.Marking ι A)
    (H : AlgebraicGeometry.ComplexMultiplication.WeightOne.CM.WeightOneHodgeStructure (A.variety.rationalCohomology 1))
    (x : AlgebraicGeometry.ComplexMultiplication.WeightOne.CM.Complexification (ι → ℚ)) :
    MarkedAbelianPeriods.IntrinsicPeriods.markedBetti b (AlgebraicGeometry.HodgeConjecture.DegreeTwo.Transport.Constructions.h1ComplexificationEquiv A.variety H
      ((rationalCoordinates b).symm.toLinearMap.baseChange ℂ x)) = scalarMarkedBetti x := by
  change (Pi.basisFun ℂ ι).constr ℂ
      (MarkedAbelianPeriods.IntrinsicPeriods.complexCoordinates b (AlgebraicGeometry.HodgeConjecture.DegreeTwo.Transport.Constructions.h1ComplexificationEquiv A.variety H
        ((rationalCoordinates b).symm.toLinearMap.baseChange ℂ x))) = _
  rw [complexCoordinates_baseChange, rationalCoordinates_baseChange_symm]
  rfl

/-- The canonical marked rational Hodge subspace is exactly the native
marked holomorphic Betti subspace under the fixed scalar-coordinate map. -/
theorem markedHodge_holomorphic_iff {A : AlgebraicGeometry.ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety} (b : MarkedAbelianPeriods.IntrinsicPeriods.Marking ι A)
    (H : AlgebraicGeometry.ComplexMultiplication.WeightOne.CM.WeightOneHodgeStructure (A.variety.rationalCohomology 1))
    (hH : AlgebraicGeometry.HodgeConjecture.DegreeTwo.Transport.Constructions.IsCanonicalH1 A.variety H) (x : AlgebraicGeometry.ComplexMultiplication.WeightOne.CM.Complexification (ι → ℚ)) :
    x ∈ (markedHodgeStructure b H).holomorphic ↔
      scalarMarkedBetti x ∈ MarkedAbelianPeriods.IntrinsicPeriods.markedHolomorphic b := by
  change (rationalCoordinates b).symm.toLinearMap.baseChange ℂ x ∈ H.holomorphic ↔ _
  rw [hH.1]
  change AlgebraicGeometry.HodgeConjecture.DegreeTwo.Transport.Constructions.h1ComplexificationEquiv A.variety H
    ((rationalCoordinates b).symm.toLinearMap.baseChange ℂ x) ∈
      A.variety.pureBettiSubspace 1 0 ↔ _
  constructor
  · intro hx
    exact ⟨_, hx, markedBetti_symm_baseChange b H x⟩
  · rintro ⟨y, hy, he⟩
    have hy' : AlgebraicGeometry.HodgeConjecture.DegreeTwo.Transport.Constructions.h1ComplexificationEquiv A.variety H
        ((rationalCoordinates b).symm.toLinearMap.baseChange ℂ x) = y := by
      apply (MarkedAbelianPeriods.IntrinsicPeriods.markedBetti b).injective
      rw [markedBetti_symm_baseChange]
      exact he.symm
    rw [hy']
    exact hy

theorem markedHodge_holomorphic_image {A : AlgebraicGeometry.ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety} (b : MarkedAbelianPeriods.IntrinsicPeriods.Marking ι A)
    (H : AlgebraicGeometry.ComplexMultiplication.WeightOne.CM.WeightOneHodgeStructure (A.variety.rationalCohomology 1))
    (hH : AlgebraicGeometry.HodgeConjecture.DegreeTwo.Transport.Constructions.IsCanonicalH1 A.variety H) :
    (markedHodgeStructure b H).holomorphic.map scalarMarkedBetti.toLinearMap =
      MarkedAbelianPeriods.IntrinsicPeriods.markedHolomorphic b := by
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact (markedHodge_holomorphic_iff b H hH x).mp hx
  · intro hy
    refine ⟨scalarMarkedBetti.symm y, ?_, scalarMarkedBetti.apply_symm_apply y⟩
    apply (markedHodge_holomorphic_iff b H hH _).mpr
    simpa only [LinearEquiv.apply_symm_apply] using hy

end

/-!
The exact marked-period classification of actual abelian varieties.
Preservation of the marked native exponential map by an algebraic group
map forces inclusion of period kernels, using discreteness of the actual
period lattice. This gives both directions of the classification.
-/

open _root_.CategoryTheory
open OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.AbelianUniformizationEq.Constructions.AbelianUniformization
open OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.IntrinsicWeight.Constructions.IntrinsicTorusMaps
open scoped _root_.CategoryTheory.MonObj

variable {Index : Type} [Fintype Index]

theorem zero_of_all_smul_mem_lattice (A : AlgebraicGeometry.ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety) (v : AlgebraicGeometry.HodgeConjecture.DegreeTwo.Transport.Constructions.AbelianModel A)
    (hv : ∀ c : ℂ, c • v ∈ AlgebraicGeometry.HodgeConjecture.DegreeTwo.AbelianUniformizationEq.Constructions.AbelianUniformization.periodLattice A) : v = 0 := by
  let f : ℂ → AlgebraicGeometry.HodgeConjecture.DegreeTwo.AbelianUniformizationEq.Constructions.AbelianUniformization.periodLattice A := fun c => ⟨c • v, hv c⟩
  have hf : Continuous f := (continuous_id.smul continuous_const).subtype_mk _
  have he : f 1 = f 0 := PreconnectedSpace.constant inferInstance hf
  have h := congrArg (fun l : AlgebraicGeometry.HodgeConjecture.DegreeTwo.AbelianUniformizationEq.Constructions.AbelianUniformization.periodLattice A => (l : AlgebraicGeometry.HodgeConjecture.DegreeTwo.Transport.Constructions.AbelianModel A)) he
  simpa only [f, one_smul, zero_smul] using h

theorem native_zero (A : AlgebraicGeometry.ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety) :
    AlgebraicGeometry.HodgeConjecture.DegreeTwo.AbelianUniformizationEq.Constructions.AbelianUniformization.periodHomeomorph IntrinsicHodgeMaps.Abelian.IntrinsicPeriods.algebraization A 0 = (1 : AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints A.toOver) :=
  (AlgebraicGeometry.HodgeConjecture.DegreeTwo.IntrinsicWeight.Constructions.IntrinsicTorusMaps.periodAddEquiv IntrinsicHodgeMaps.Abelian.IntrinsicPeriods.algebraization A).map_zero

/-- An algebraic group map respecting the marking preserves its period kernel. -/
theorem period_ker_le_of_marked_map (A B : AlgebraicGeometry.ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety)
    (a : MarkedAbelianPeriods.IntrinsicPeriods.Marking Index A) (b : MarkedAbelianPeriods.IntrinsicPeriods.Marking Index B) (f : A.toOver ⟶ B.toOver) [IsMonHom f]
    (hf : ∀ z : Index → ℂ,
      AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map f
        (AlgebraicGeometry.HodgeConjecture.DegreeTwo.AbelianUniformizationEq.Constructions.AbelianUniformization.periodHomeomorph IntrinsicHodgeMaps.Abelian.IntrinsicPeriods.algebraization A ((IntrinsicHodgeMaps.Abelian.IntrinsicPeriods.torus A).proj (MarkedAbelianPeriods.IntrinsicPeriods.periodMap a z))) =
          AlgebraicGeometry.HodgeConjecture.DegreeTwo.AbelianUniformizationEq.Constructions.AbelianUniformization.periodHomeomorph IntrinsicHodgeMaps.Abelian.IntrinsicPeriods.algebraization B ((IntrinsicHodgeMaps.Abelian.IntrinsicPeriods.torus B).proj (MarkedAbelianPeriods.IntrinsicPeriods.periodMap b z))) :
    (MarkedAbelianPeriods.IntrinsicPeriods.periodMap a).ker ≤ (MarkedAbelianPeriods.IntrinsicPeriods.periodMap b).ker := by
  intro z hz
  change MarkedAbelianPeriods.IntrinsicPeriods.periodMap b z = 0
  apply zero_of_all_smul_mem_lattice B
  intro c
  have h := hf (c • z)
  have ha : MarkedAbelianPeriods.IntrinsicPeriods.periodMap a (c • z) = 0 := by rw [map_smul, hz, smul_zero]
  rw [ha] at h
  change AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map f (AlgebraicGeometry.HodgeConjecture.DegreeTwo.AbelianUniformizationEq.Constructions.AbelianUniformization.periodHomeomorph IntrinsicHodgeMaps.Abelian.IntrinsicPeriods.algebraization A 0) =
    AlgebraicGeometry.HodgeConjecture.DegreeTwo.AbelianUniformizationEq.Constructions.AbelianUniformization.periodHomeomorph IntrinsicHodgeMaps.Abelian.IntrinsicPeriods.algebraization B ((IntrinsicHodgeMaps.Abelian.IntrinsicPeriods.torus B).proj (MarkedAbelianPeriods.IntrinsicPeriods.periodMap b (c • z))) at h
  rw [native_zero] at h
  have hf1 : AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map f 1 = 1 := MonObj.one_comp f
  rw [hf1, ← native_zero B] at h
  have he := (AlgebraicGeometry.HodgeConjecture.DegreeTwo.AbelianUniformizationEq.Constructions.AbelianUniformization.periodHomeomorph IntrinsicHodgeMaps.Abelian.IntrinsicPeriods.algebraization B).injective h
  change (0 : (IntrinsicHodgeMaps.Abelian.IntrinsicPeriods.torus B).Point) = (IntrinsicHodgeMaps.Abelian.IntrinsicPeriods.torus B).proj (MarkedAbelianPeriods.IntrinsicPeriods.periodMap b (c • z)) at he
  have hz' : (IntrinsicHodgeMaps.Abelian.IntrinsicPeriods.torus B).proj (c • MarkedAbelianPeriods.IntrinsicPeriods.periodMap b z) = 0 := by
    simpa only [map_smul] using he.symm
  exact ((IntrinsicHodgeMaps.Abelian.IntrinsicPeriods.torus B).proj_eq_zero _).mp hz'

/-- The marking condition uses every complex period vector, so it records
the full linear period map and not just the identity values of integral loops. -/
def HasMarkedGroupIso (A B : AlgebraicGeometry.ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety) (a : MarkedAbelianPeriods.IntrinsicPeriods.Marking Index A) (b : MarkedAbelianPeriods.IntrinsicPeriods.Marking Index B) : Prop :=
  ∃ e : A.toOver ≅ B.toOver, IsMonHom e.hom ∧
    ∀ z : Index → ℂ,
      AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map e.hom
        (AlgebraicGeometry.HodgeConjecture.DegreeTwo.AbelianUniformizationEq.Constructions.AbelianUniformization.periodHomeomorph IntrinsicHodgeMaps.Abelian.IntrinsicPeriods.algebraization A ((IntrinsicHodgeMaps.Abelian.IntrinsicPeriods.torus A).proj (MarkedAbelianPeriods.IntrinsicPeriods.periodMap a z))) =
          AlgebraicGeometry.HodgeConjecture.DegreeTwo.AbelianUniformizationEq.Constructions.AbelianUniformization.periodHomeomorph IntrinsicHodgeMaps.Abelian.IntrinsicPeriods.algebraization B ((IntrinsicHodgeMaps.Abelian.IntrinsicPeriods.torus B).proj (MarkedAbelianPeriods.IntrinsicPeriods.periodMap b z))

theorem period_eq_iff_marked_group_iso (A B : AlgebraicGeometry.ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety)
    (a : MarkedAbelianPeriods.IntrinsicPeriods.Marking Index A) (b : MarkedAbelianPeriods.IntrinsicPeriods.Marking Index B) :
    (MarkedAbelianPeriods.IntrinsicPeriods.periodMap a).ker = (MarkedAbelianPeriods.IntrinsicPeriods.periodMap b).ker ↔ HasMarkedGroupIso A B a b := by
  constructor
  · exact MarkedAbelianPeriods.IntrinsicPeriods.algebraic_iso_of_marked_period_eq A B a b
  · rintro ⟨e, he, hp⟩
    let : IsMonHom e.hom := he
    have hip (z : Index → ℂ) :
        AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map e.inv
          (AlgebraicGeometry.HodgeConjecture.DegreeTwo.AbelianUniformizationEq.Constructions.AbelianUniformization.periodHomeomorph IntrinsicHodgeMaps.Abelian.IntrinsicPeriods.algebraization B ((IntrinsicHodgeMaps.Abelian.IntrinsicPeriods.torus B).proj (MarkedAbelianPeriods.IntrinsicPeriods.periodMap b z))) =
            AlgebraicGeometry.HodgeConjecture.DegreeTwo.AbelianUniformizationEq.Constructions.AbelianUniformization.periodHomeomorph IntrinsicHodgeMaps.Abelian.IntrinsicPeriods.algebraization A ((IntrinsicHodgeMaps.Abelian.IntrinsicPeriods.torus A).proj (MarkedAbelianPeriods.IntrinsicPeriods.periodMap a z)) := by
      rw [← hp]
      change (_ ≫ e.hom) ≫ e.inv = _
      rw [Category.assoc, e.hom_inv_id, Category.comp_id]
    exact le_antisymm (period_ker_le_of_marked_map A B a b e.hom hp)
      (period_ker_le_of_marked_map B A b a e.inv hip)

theorem markedHolomorphic_eq_iff_marked_group_iso (A B : AlgebraicGeometry.ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety)
    (a : MarkedAbelianPeriods.IntrinsicPeriods.Marking Index A) (b : MarkedAbelianPeriods.IntrinsicPeriods.Marking Index B) :
    MarkedAbelianPeriods.IntrinsicPeriods.markedHolomorphic a = MarkedAbelianPeriods.IntrinsicPeriods.markedHolomorphic b ↔ HasMarkedGroupIso A B a b := by
  rw [MarkedAbelianPeriods.IntrinsicPeriods.markedHolomorphic_eq_annihilator, MarkedAbelianPeriods.IntrinsicPeriods.markedHolomorphic_eq_annihilator,
    Subspace.dualAnnihilator_inj, period_eq_iff_marked_group_iso]

/-- The classification also uses the canonically transported rational Hodge
structures, with their fixed coefficient complexification. -/
theorem markedHodge_eq_iff_marked_group_iso (A B : AlgebraicGeometry.ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety)
    (a : MarkedAbelianPeriods.IntrinsicPeriods.Marking Index A) (b : MarkedAbelianPeriods.IntrinsicPeriods.Marking Index B)
    (HA : AlgebraicGeometry.ComplexMultiplication.WeightOne.CM.WeightOneHodgeStructure (A.variety.rationalCohomology 1))
    (HB : AlgebraicGeometry.ComplexMultiplication.WeightOne.CM.WeightOneHodgeStructure (B.variety.rationalCohomology 1))
    (hHA : AlgebraicGeometry.HodgeConjecture.DegreeTwo.Transport.Constructions.IsCanonicalH1 A.variety HA) (hHB : AlgebraicGeometry.HodgeConjecture.DegreeTwo.Transport.Constructions.IsCanonicalH1 B.variety HB) :
    (markedHodgeStructure a HA).holomorphic = (markedHodgeStructure b HB).holomorphic ↔
      HasMarkedGroupIso A B a b := by
  rw [← markedHolomorphic_eq_iff_marked_group_iso]
  constructor
  · intro h
    rw [← markedHodge_holomorphic_image a HA hHA, ← markedHodge_holomorphic_image b HB hHB, h]
  · intro h
    ext x
    rw [markedHodge_holomorphic_iff a HA hHA, h, ← markedHodge_holomorphic_iff b HB hHB]

end

end OAI.ArithmeticGeometry.Descent.CMVariety.MarkedPeriodClassification.Abelian.IntrinsicPeriods

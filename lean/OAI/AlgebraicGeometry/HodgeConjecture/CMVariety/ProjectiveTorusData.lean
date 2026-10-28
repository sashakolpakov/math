import OAI.AlgebraicGeometry.HodgeConjecture.CMVariety.PeriodCoordinatesReal
import OAI.AlgebraicGeometry.HodgeConjecture.CMVariety.RiemannForm
import OAI.AlgebraicGeometry.HodgeConjecture.CMVariety.IntegralLattice
import OAI.Geometry.ComplexTorus.RiemannProjectivity.ProjectivityCriterion

/-! # Projective Torus Data -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.CMVariety.ProjectiveTorusData.CM.Abelian

noncomputable section

section

/-! The compact, polarized generic period torus and the application of RiemannProjectivity. -/

open scoped TensorProduct

/-- The exact generic projectivity criterion in the committed RiemannProjectivity specification. -/
def RiemannProjectivityInput : Prop :=
  ∀ (V : Type) [NormedAddCommGroup V] [NormedSpace ℂ V]
    [FiniteDimensional ℂ V] (Λ : AddSubgroup V)
    [DiscreteTopology Λ] [CompactSpace (V ⧸ Λ)],
    Geometry.ComplexTorus.RiemannProjectivity.ProjectivityCriterion.IsProjectiveComplexTorus V Λ ↔
      ∃ H : V →ₗ⋆[ℂ] V →ₗ[ℂ] ℂ,
        (∀ u v : V, H v u = star (H u v)) ∧
        (∀ u : V, u ≠ 0 → 0 < (H u u).re) ∧
        (∀ u ∈ Λ, ∀ v ∈ Λ,
          ∃ m : ℤ, (H u v).im = (m : ℝ))

variable {U : Type} [AddCommGroup U] [Module ℚ U]

abbrev GenericPeriodSpace (H : ComplexMultiplication.WeightOne.CM.WeightOneHodgeStructure U) :=
  Fin (Module.finrank ℂ H.antiholomorphic) → ℂ

def periodComplexEquiv (H : ComplexMultiplication.WeightOne.CM.WeightOneHodgeStructure U) :
    H.antiholomorphic ≃ₗ[ℂ] GenericPeriodSpace H := by
  letI : Module.Finite ℚ U := H.finiteDimensional
  exact (Module.finBasis ℂ H.antiholomorphic).equivFun

variable {ι : Type} [Fintype ι] [DecidableEq ι]
    (b : Module.Basis ι ℚ U) (H : ComplexMultiplication.WeightOne.CM.WeightOneHodgeStructure U)

def genericPeriodBasis : Module.Basis ι ℝ (GenericPeriodSpace H) :=
  (PeriodCoordinatesReal.CM.Abelian.periodRealBasis b H).map ((periodComplexEquiv H).restrictScalars ℝ)

def genericPeriodLattice : Submodule ℤ (GenericPeriodSpace H) :=
  Submodule.span ℤ (Set.range (genericPeriodBasis b H))

instance genericPeriodLattice_discrete : DiscreteTopology (genericPeriodLattice b H) := by
  unfold genericPeriodLattice
  infer_instance

instance genericPeriodLattice_full : IsZLattice ℝ (genericPeriodLattice b H) := by
  unfold genericPeriodLattice
  infer_instance

abbrev GenericPeriodTorus :=
  GenericPeriodSpace H ⧸ (genericPeriodLattice b H).toAddSubgroup

instance genericPeriodTorus_compact : CompactSpace (GenericPeriodTorus b H) := by
  apply isCompact_univ_iff.mp
  have hc := IsZLattice.isCompact_range_of_periodic (genericPeriodLattice b H)
    (QuotientAddGroup.mk : GenericPeriodSpace H → GenericPeriodTorus b H)
    QuotientAddGroup.continuous_mk (by
      intro z w hw
      rw [QuotientAddGroup.mk_add, (QuotientAddGroup.eq_zero_iff w).mpr hw, add_zero])
  rwa [Set.range_eq_univ.mpr QuotientAddGroup.mk_surjective] at hc

instance genericPeriodTorus_t2 : T2Space (GenericPeriodTorus b H) := by
  let : DiscreteTopology (genericPeriodLattice b H).toAddSubgroup :=
    genericPeriodLattice_discrete b H
  let : IsClosed ((genericPeriodLattice b H).toAddSubgroup : Set (GenericPeriodSpace H)) :=
    AddSubgroup.isClosed_of_discreteTopology
  infer_instance

variable {H} (P : ComplexMultiplication.CM.Polarization.WeightOnePolarization H)

def genericPeriodHermitian :
    GenericPeriodSpace H →ₗ⋆[ℂ] GenericPeriodSpace H →ₗ[ℂ] ℂ :=
  ((RiemannForm.CM.Abelian.periodHermitian P).comp (periodComplexEquiv H).symm.toLinearMap).compl₂
    (periodComplexEquiv H).symm.toLinearMap

theorem genericPeriodHermitian_symm (x y : GenericPeriodSpace H) :
    genericPeriodHermitian P y x = star (genericPeriodHermitian P x y) :=
  RiemannForm.CM.Abelian.periodHermitian_symm P _ _

theorem genericPeriodHermitian_positive (x : GenericPeriodSpace H) (hx : x ≠ 0) :
    0 < (genericPeriodHermitian P x x).re := by
  apply RiemannForm.CM.Abelian.periodHermitian_positive P
  intro hz
  apply hx
  simpa using congrArg (periodComplexEquiv H) hz

/-- The imaginary part is a real bilinear form, so integrality extends from basis pairs. -/
def genericPeriodImaginary : LinearMap.BilinForm ℝ (GenericPeriodSpace H) where
  toFun x :=
    { toFun := fun y => (genericPeriodHermitian P x y).im
      map_add' := by intro y z; simp
      map_smul' := by
        intro r y
        change ((((genericPeriodHermitian P x).restrictScalars ℝ) (r • y))).im = _
        rw [map_smul]
        simp }
  map_add' := by intro x y; ext z; simp
  map_smul' := by
    intro r x
    apply LinearMap.ext
    intro y
    change (genericPeriodHermitian P (r • x) y).im = _
    rw [← IsScalarTower.algebraMap_smul ℂ r x, map_smulₛₗ]
    simp

theorem genericPeriodBasis_realVector (i : ι) :
    (((PeriodSpace.CM.Abelian.periodRealEquiv H).symm
      ((periodComplexEquiv H).symm (genericPeriodBasis b H i))) : ComplexMultiplication.WeightOne.CM.Complexification U) =
      (1 : ℂ) ⊗ₜ[ℚ] b i := by
  change (((PeriodSpace.CM.Abelian.periodRealEquiv H).symm ((periodComplexEquiv H).symm
    (periodComplexEquiv H (PeriodSpace.CM.Abelian.periodRealEquiv H
      ((PeriodCoordinatesReal.CM.Abelian.realCoordinateEquiv b).symm ((Pi.basisFun ℝ ι) i)))))) : ComplexMultiplication.WeightOne.CM.Complexification U) = _
  rw [LinearEquiv.symm_apply_apply, LinearEquiv.symm_apply_apply]
  exact PeriodCoordinatesReal.CM.Abelian.realCoordinateEquiv_symm_basis b i

theorem genericPeriodHermitian_basis_imaginary (i j : ι) :
    ((genericPeriodHermitian P (genericPeriodBasis b H i) (genericPeriodBasis b H j)).im : ℂ) =
      (P.form (b i) (b j) : ℂ) := by
  change ((RiemannForm.CM.Abelian.periodHermitian P _ _).im : ℂ) = _
  rw [RiemannForm.CM.Abelian.periodHermitian_imaginary,
    ← PeriodSpace.CM.Abelian.periodRealEquiv_symm_coe H, ← PeriodSpace.CM.Abelian.periodRealEquiv_symm_coe H]
  change P.form.baseChange ℂ
    (((PeriodSpace.CM.Abelian.periodRealEquiv H).symm ((periodComplexEquiv H).symm
      (genericPeriodBasis b H i))) : ComplexMultiplication.WeightOne.CM.Complexification U)
    (((PeriodSpace.CM.Abelian.periodRealEquiv H).symm ((periodComplexEquiv H).symm
      (genericPeriodBasis b H j))) : ComplexMultiplication.WeightOne.CM.Complexification U) = _
  rw [genericPeriodBasis_realVector b (H := H) i, genericPeriodBasis_realVector b (H := H) j]
  simp

theorem genericPeriodHermitian_integral
    (hint : ∀ x ∈ Submodule.span ℤ (Set.range b),
      ∀ y ∈ Submodule.span ℤ (Set.range b),
        IsLocalization.IsInteger ℤ (P.form x y)) :
    ∀ x ∈ (genericPeriodLattice b H).toAddSubgroup,
      ∀ y ∈ (genericPeriodLattice b H).toAddSubgroup,
        ∃ m : ℤ, (genericPeriodHermitian P x y).im = (m : ℝ) := by
  have hb : ∀ x ∈ Set.range (genericPeriodBasis b H),
      ∀ y ∈ Set.range (genericPeriodBasis b H),
        IsLocalization.IsInteger ℤ (genericPeriodImaginary P x y) := by
    rintro x ⟨i, rfl⟩ y ⟨j, rfl⟩
    obtain ⟨m, hm⟩ := hint (b i) (Submodule.subset_span ⟨i, rfl⟩)
      (b j) (Submodule.subset_span ⟨j, rfl⟩)
    refine ⟨m, ?_⟩
    change (m : ℝ) = (genericPeriodHermitian P (genericPeriodBasis b H i)
      (genericPeriodBasis b H j)).im
    have he := genericPeriodHermitian_basis_imaginary b P i j
    change (m : ℚ) = P.form (b i) (b j) at hm
    rw [← hm] at he
    have hre := congrArg Complex.re he
    simpa using hre.symm
  intro x hx y hy
  obtain ⟨m, hm⟩ := IntegralLattice.CM.Abelian.integer_bilin_on_span (genericPeriodImaginary P)
    (Set.range (genericPeriodBasis b H)) hb x hx y hy
  exact ⟨m, hm.symm⟩

include P in
/-- RiemannProjectivity gives a closed holomorphic projective embedding of the constructed generic torus. -/
theorem generic_period_torus_projective
    (hRiemannProjectivity : RiemannProjectivityInput) :
    Geometry.ComplexTorus.RiemannProjectivity.ProjectivityCriterion.IsProjectiveComplexTorus
      (GenericPeriodSpace H) (genericPeriodLattice b H).toAddSubgroup := by
  obtain ⟨P', hint⟩ := IntegralLattice.CM.Abelian.exists_integral_polarization P b
  let : DiscreteTopology (genericPeriodLattice b H).toAddSubgroup :=
    genericPeriodLattice_discrete b H
  exact (hRiemannProjectivity (GenericPeriodSpace H) (genericPeriodLattice b H).toAddSubgroup).mpr
    ⟨genericPeriodHermitian P', genericPeriodHermitian_symm P',
      genericPeriodHermitian_positive P', genericPeriodHermitian_integral b P' hint⟩

end

/-!
Data already constructed before algebraization: a finite-dimensional complex
vector space, a discrete full integer lattice, and the analytic projective
embedding supplied by RiemannProjectivity. The constructor below exhibits every field from
the actual generic Hodge structure and its polarization. No algebraic variety,
Hodge realization, or cohomological comparison is a field of this structure.
-/

structure ProjectivePeriodData where
  space : Type
  [normed : NormedAddCommGroup space]
  [complex : NormedSpace ℂ space]
  [real : NormedSpace ℝ space]
  [tower : IsScalarTower ℝ ℂ space]
  [finite : FiniteDimensional ℂ space]
  periodIntegerLattice : Submodule ℤ space
  [periodIntegerLattice_discrete : DiscreteTopology periodIntegerLattice]
  [periodIntegerLattice_full : IsZLattice ℝ periodIntegerLattice]
  projective : Geometry.ComplexTorus.RiemannProjectivity.ProjectivityCriterion.IsProjectiveComplexTorus space periodIntegerLattice.toAddSubgroup

attribute [instance] ProjectivePeriodData.normed ProjectivePeriodData.complex
  ProjectivePeriodData.real ProjectivePeriodData.tower ProjectivePeriodData.finite
  ProjectivePeriodData.periodIntegerLattice_discrete ProjectivePeriodData.periodIntegerLattice_full

namespace ProjectivePeriodData

instance realFinite (D : ProjectivePeriodData) : FiniteDimensional ℝ D.space :=
  FiniteDimensional.trans ℝ ℂ D.space

abbrev periodTorus (D : ProjectivePeriodData) :=
  D.space ⧸ D.periodIntegerLattice.toAddSubgroup

instance periodTorus_compact (D : ProjectivePeriodData) : CompactSpace D.periodTorus := by
  apply isCompact_univ_iff.mp
  have hc := IsZLattice.isCompact_range_of_periodic D.periodIntegerLattice
    (QuotientAddGroup.mk : D.space → D.periodTorus)
    QuotientAddGroup.continuous_mk (by
      intro z w hw
      rw [QuotientAddGroup.mk_add, (QuotientAddGroup.eq_zero_iff w).mpr hw, add_zero])
  rwa [Set.range_eq_univ.mpr QuotientAddGroup.mk_surjective] at hc

instance periodTorus_t2 (D : ProjectivePeriodData) : T2Space D.periodTorus := by
  let : DiscreteTopology D.periodIntegerLattice.toAddSubgroup :=
    D.periodIntegerLattice_discrete
  let : IsClosed (D.periodIntegerLattice.toAddSubgroup : Set D.space) :=
    AddSubgroup.isClosed_of_discreteTopology
  infer_instance

def ofHodgeStructure {U ι : Type} [AddCommGroup U] [Module ℚ U]
    [Fintype ι] [DecidableEq ι] (b : Module.Basis ι ℚ U)
    (H : ComplexMultiplication.WeightOne.CM.WeightOneHodgeStructure U) (P : ComplexMultiplication.CM.Polarization.WeightOnePolarization H)
    (hRiemannProjectivity : RiemannProjectivityInput) : ProjectivePeriodData where
  space := GenericPeriodSpace H
  periodIntegerLattice := genericPeriodLattice b H
  projective := generic_period_torus_projective b P hRiemannProjectivity

end ProjectivePeriodData

end

end OAI.AlgebraicGeometry.HodgeConjecture.CMVariety.ProjectiveTorusData.CM.Abelian

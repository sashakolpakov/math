import OAI.AlgebraicGeometry.ComplexMultiplication.GaloisCMType
import OAI.AlgebraicGeometry.ComplexMultiplication.CM.PeriodHermitian
import OAI.AlgebraicGeometry.ComplexMultiplication.CM.PeriodTorus
import OAI.AlgebraicGeometry.ComplexPoints.Analytic.ProjectiveCharts
import Mathlib.LinearAlgebra.SesquilinearForm.Star
import Mathlib.Analysis.Calculus.FDeriv.Mul

/-! # Fin -/

namespace OAI.Geometry.ComplexTorus.RiemannProjectivity.Fin.Constructions

noncomputable section

/-!
# RiemannProjectivity: CM sign realization, projective analytic construction

This file does not import any statement stub. `RiemannProjectivityInput`
reproduces the RiemannProjectivity statement as a named hypothesis. The Boolean signs and
the period lattice are those of the existing CM construction. WeakApproximation and AuxiliaryApproximation
are not needed for this step: the library already proves the imaginary-element,
integral-polarization, full-lattice, and complex-Lie-group constructions.

The theorems below establish the analytic projective torus. The actual rational
cohomology and both Hodge comparisons are proved in `AnalyticRealization`.
The algebraic group and native Hodge comparison are completed in
`Realization`; `RiemannProjectivityFinal` discharges RiemannProjectivity and proves the exact manuscript theorem.
-/

open scoped _root_.NumberField _root_.Topology

open OAI.AlgebraicGeometry.Foundations.Scheme.ProjectiveCoordinatesIn.Algebraic.ProjectiveCoordinates
open Filter

section ProjectiveDifferentiability

variable {V ι : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]
  [Fintype ι]

/-- The rational coordinate change between two projective patches. -/
def normalizeCoordinates (i : ι) (z : ι → ℂ) : ι → ℂ :=
  fun j => z j / z i

theorem normalizeCoordinates_differentiableAt (i : ι) (z : ι → ℂ)
    (hz : z i ≠ 0) : DifferentiableAt ℂ (normalizeCoordinates i) z := by
  apply differentiableAt_pi.mpr
  intro j
  convert!
    (differentiableAt_apply (𝕜 := ℂ) j z).mul
      ((differentiableAt_apply (𝕜 := ℂ) i z).inv hz) using 1

omit [NormedSpace ℂ V] [Fintype ι] in
/-- The ratio formula holds on a neighborhood whenever the source chart is
valid at the point. This uses the ordinary projective topology. -/
theorem coordinates_eventually_change
    (f : V → Projectivization ℂ (ι → ℂ)) {x : V}
    (hf : ContinuousAt f x) (i j : ι) (hi : AlgebraicGeometry.Foundations.Scheme.ProjectiveCoordinatesIn.Algebraic.ProjectiveCoordinates.InPatch i (f x)) :
    (fun y => AlgebraicGeometry.Foundations.Scheme.ProjectiveCoordinatesIn.Algebraic.ProjectiveCoordinates.coordinates j (f y)) =ᶠ[𝓝 x]
      (fun y => normalizeCoordinates j (AlgebraicGeometry.Foundations.Scheme.ProjectiveCoordinatesIn.Algebraic.ProjectiveCoordinates.coordinates i (f y))) := by
  have hpatch : ∀ᶠ y in 𝓝 x, AlgebraicGeometry.Foundations.Scheme.ProjectiveCoordinatesIn.Algebraic.ProjectiveCoordinates.InPatch i (f y) :=
    hf.preimage_mem_nhds (AlgebraicGeometry.ComplexPoints.Analytic.ProjectiveCharts.isOpen_projectivePatch i |>.mem_nhds hi)
  filter_upwards [hpatch] with y hy
  funext k
  exact AlgebraicGeometry.Foundations.Scheme.ProjectiveCoordinatesIn.Algebraic.ProjectiveCoordinates.transition_formula i j k (f y) hy

/-- Differentiability in one valid projective chart implies differentiability
in every valid projective chart, using the actual rational transition. -/
theorem coordinates_differentiableAt_change
    (f : V → Projectivization ℂ (ι → ℂ)) {x : V}
    (hf : ContinuousAt f x) (i j : ι)
    (hi : AlgebraicGeometry.Foundations.Scheme.ProjectiveCoordinatesIn.Algebraic.ProjectiveCoordinates.InPatch i (f x)) (hj : AlgebraicGeometry.Foundations.Scheme.ProjectiveCoordinatesIn.Algebraic.ProjectiveCoordinates.InPatch j (f x))
    (hd : DifferentiableAt ℂ (fun y => AlgebraicGeometry.Foundations.Scheme.ProjectiveCoordinatesIn.Algebraic.ProjectiveCoordinates.coordinates i (f y)) x) :
    DifferentiableAt ℂ (fun y => AlgebraicGeometry.Foundations.Scheme.ProjectiveCoordinatesIn.Algebraic.ProjectiveCoordinates.coordinates j (f y)) x := by
  have hn : AlgebraicGeometry.Foundations.Scheme.ProjectiveCoordinatesIn.Algebraic.ProjectiveCoordinates.coordinates i (f x) j ≠ 0 :=
    (AlgebraicGeometry.Foundations.Scheme.ProjectiveCoordinatesIn.Algebraic.ProjectiveCoordinates.inPatch_iff_ratio_ne_zero i j (f x) hi).mp hj
  have hcomp : DifferentiableAt ℂ
      (fun y => normalizeCoordinates j (AlgebraicGeometry.Foundations.Scheme.ProjectiveCoordinatesIn.Algebraic.ProjectiveCoordinates.coordinates i (f y))) x :=
    by convert! (normalizeCoordinates_differentiableAt j _ hn).comp x hd using 1
  exact hcomp.congr_of_eventuallyEq (coordinates_eventually_change f hf i j hi)

/-- Injectivity of a coordinate differential is independent of the valid
projective chart. The reverse transition factors the given differential. -/
theorem coordinates_injective_fderiv_change
    (f : V → Projectivization ℂ (ι → ℂ)) {x : V}
    (hf : ContinuousAt f x) (i j : ι)
    (hi : AlgebraicGeometry.Foundations.Scheme.ProjectiveCoordinatesIn.Algebraic.ProjectiveCoordinates.InPatch i (f x)) (hj : AlgebraicGeometry.Foundations.Scheme.ProjectiveCoordinatesIn.Algebraic.ProjectiveCoordinates.InPatch j (f x))
    (hd : DifferentiableAt ℂ (fun y => AlgebraicGeometry.Foundations.Scheme.ProjectiveCoordinatesIn.Algebraic.ProjectiveCoordinates.coordinates i (f y)) x)
    (hinj : Function.Injective (fderiv ℂ (fun y => AlgebraicGeometry.Foundations.Scheme.ProjectiveCoordinatesIn.Algebraic.ProjectiveCoordinates.coordinates i (f y)) x)) :
    Function.Injective (fderiv ℂ (fun y => AlgebraicGeometry.Foundations.Scheme.ProjectiveCoordinatesIn.Algebraic.ProjectiveCoordinates.coordinates j (f y)) x) := by
  have hdj := coordinates_differentiableAt_change f hf i j hi hj hd
  have hn : AlgebraicGeometry.Foundations.Scheme.ProjectiveCoordinatesIn.Algebraic.ProjectiveCoordinates.coordinates j (f x) i ≠ 0 :=
    (AlgebraicGeometry.Foundations.Scheme.ProjectiveCoordinatesIn.Algebraic.ProjectiveCoordinates.inPatch_iff_ratio_ne_zero j i (f x) hj).mp hi
  have heq := coordinates_eventually_change f hf j i hj
  have hderiv : fderiv ℂ (fun y => AlgebraicGeometry.Foundations.Scheme.ProjectiveCoordinatesIn.Algebraic.ProjectiveCoordinates.coordinates i (f y)) x =
      (fderiv ℂ (normalizeCoordinates i) (AlgebraicGeometry.Foundations.Scheme.ProjectiveCoordinatesIn.Algebraic.ProjectiveCoordinates.coordinates j (f x))).comp
        (fderiv ℂ (fun y => AlgebraicGeometry.Foundations.Scheme.ProjectiveCoordinatesIn.Algebraic.ProjectiveCoordinates.coordinates j (f y)) x) := by
    rw [heq.fderiv_eq]
    exact fderiv_comp x (normalizeCoordinates_differentiableAt i _ hn) hdj
  intro u w huw
  apply hinj
  rw [hderiv]
  exact congrArg (fderiv ℂ (normalizeCoordinates i) (AlgebraicGeometry.Foundations.Scheme.ProjectiveCoordinatesIn.Algebraic.ProjectiveCoordinates.coordinates j (f x))) huw

/-- Local chart choices in RiemannProjectivity yield holomorphic coordinates throughout each
fixed standard projective patch. -/
theorem coordinates_differentiableOn_patch
    (f : V → Projectivization ℂ (ι → ℂ)) (hf : Continuous f)
    (hd : ∀ x, ∃ i, AlgebraicGeometry.Foundations.Scheme.ProjectiveCoordinatesIn.Algebraic.ProjectiveCoordinates.InPatch i (f x) ∧
      DifferentiableAt ℂ (fun y => AlgebraicGeometry.Foundations.Scheme.ProjectiveCoordinatesIn.Algebraic.ProjectiveCoordinates.coordinates i (f y)) x) (j : ι) :
    DifferentiableOn ℂ (fun y => AlgebraicGeometry.Foundations.Scheme.ProjectiveCoordinatesIn.Algebraic.ProjectiveCoordinates.coordinates j (f y)) {x | AlgebraicGeometry.Foundations.Scheme.ProjectiveCoordinatesIn.Algebraic.ProjectiveCoordinates.InPatch j (f x)} := by
  intro x hx
  obtain ⟨i, hi, hdi⟩ := hd x
  exact (coordinates_differentiableAt_change f hf.continuousAt i j hi hx hdi).differentiableWithinAt

omit [Fintype ι] in
/-- The normalized coordinate is locally the constant one, so its
differential vanishes on every tangent vector. -/
theorem coordinates_fderiv_self_zero
    (f : V → Projectivization ℂ (ι → ℂ)) {x : V}
    (hf : ContinuousAt f x) (i : ι) (hi : AlgebraicGeometry.Foundations.Scheme.ProjectiveCoordinatesIn.Algebraic.ProjectiveCoordinates.InPatch i (f x))
    (hd : DifferentiableAt ℂ (fun y => AlgebraicGeometry.Foundations.Scheme.ProjectiveCoordinatesIn.Algebraic.ProjectiveCoordinates.coordinates i (f y)) x) (u : V) :
    fderiv ℂ (fun y => AlgebraicGeometry.Foundations.Scheme.ProjectiveCoordinatesIn.Algebraic.ProjectiveCoordinates.coordinates i (f y)) x u i = 0 := by
  have heq : (fun y => AlgebraicGeometry.Foundations.Scheme.ProjectiveCoordinatesIn.Algebraic.ProjectiveCoordinates.coordinates i (f y) i) =ᶠ[𝓝 x] (fun _ => (1 : ℂ)) := by
    have hpatch := hf.preimage_mem_nhds
      (AlgebraicGeometry.ComplexPoints.Analytic.ProjectiveCharts.isOpen_projectivePatch i |>.mem_nhds hi)
    filter_upwards [hpatch] with y hy
    exact AlgebraicGeometry.Foundations.Scheme.ProjectiveCoordinatesIn.Algebraic.ProjectiveCoordinates.coordinates_self i (f y) hy
  have hzero : fderiv ℂ (fun y => AlgebraicGeometry.Foundations.Scheme.ProjectiveCoordinatesIn.Algebraic.ProjectiveCoordinates.coordinates i (f y) i) x = 0 := by
    rw [heq.fderiv_eq]
    exact (hasFDerivAt_const (𝕜 := ℂ) (1 : ℂ) x).fderiv
  have h := (fderiv_apply hd i).symm.trans hzero
  exact congrArg (fun L : V →L[ℂ] ℂ => L u) h

end ProjectiveDifferentiability

section FiniteProjectiveCharts

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V] {n : ℕ}

/-- Removing the normalized coordinate gives a differentiable map into the
ordinary n-dimensional affine chart. -/
theorem projectiveFinChart_differentiableAt
    (f : V → Projectivization ℂ (Fin (n + 1) → ℂ)) {x : V} (i : Fin (n + 1))
    (hd : DifferentiableAt ℂ (fun y => AlgebraicGeometry.Foundations.Scheme.ProjectiveCoordinatesIn.Algebraic.ProjectiveCoordinates.coordinates i (f y)) x) :
    DifferentiableAt ℂ (fun y => AlgebraicGeometry.ComplexPoints.Analytic.ProjectiveCharts.projectiveFinChart i (f y)) x := by
  apply differentiableAt_pi.mpr
  intro k
  exact differentiableAt_pi.mp hd (i.succAbove k)

/-- Removing the constant coordinate preserves injectivity of the
differential, with no extra rank or nondegeneracy assumption. -/
theorem projectiveFinChart_injective_fderiv
    (f : V → Projectivization ℂ (Fin (n + 1) → ℂ)) {x : V}
    (hf : ContinuousAt f x) (i : Fin (n + 1)) (hi : AlgebraicGeometry.Foundations.Scheme.ProjectiveCoordinatesIn.Algebraic.ProjectiveCoordinates.InPatch i (f x))
    (hd : DifferentiableAt ℂ (fun y => AlgebraicGeometry.Foundations.Scheme.ProjectiveCoordinatesIn.Algebraic.ProjectiveCoordinates.coordinates i (f y)) x)
    (hinj : Function.Injective (fderiv ℂ (fun y => AlgebraicGeometry.Foundations.Scheme.ProjectiveCoordinatesIn.Algebraic.ProjectiveCoordinates.coordinates i (f y)) x)) :
    Function.Injective (fderiv ℂ (fun y => AlgebraicGeometry.ComplexPoints.Analytic.ProjectiveCharts.projectiveFinChart i (f y)) x) := by
  have hd' := projectiveFinChart_differentiableAt f i hd
  have hcomponent (k : Fin n) (u : V) :
      fderiv ℂ (fun y => AlgebraicGeometry.ComplexPoints.Analytic.ProjectiveCharts.projectiveFinChart i (f y)) x u k =
        fderiv ℂ (fun y => AlgebraicGeometry.Foundations.Scheme.ProjectiveCoordinatesIn.Algebraic.ProjectiveCoordinates.coordinates i (f y)) x u (i.succAbove k) := by
    calc
      _ = fderiv ℂ (fun y => AlgebraicGeometry.ComplexPoints.Analytic.ProjectiveCharts.projectiveFinChart i (f y) k) x u := by
        rw [fderiv_apply hd']
        rfl
      _ = fderiv ℂ (fun y => AlgebraicGeometry.Foundations.Scheme.ProjectiveCoordinatesIn.Algebraic.ProjectiveCoordinates.coordinates i (f y) (i.succAbove k)) x u := rfl
      _ = _ := by
        rw [fderiv_apply hd]
        rfl
  intro u w huw
  apply hinj
  funext k
  by_cases hk : k = i
  · subst k
    rw [coordinates_fderiv_self_zero f hf i hi hd u,
      coordinates_fderiv_self_zero f hf i hi hd w]
  · obtain ⟨j, rfl⟩ := Fin.exists_succAbove_eq hk
    rw [← hcomponent j u, ← hcomponent j w]
    exact congrFun huw j

end FiniteProjectiveCharts

/-- The analytic projectivity predicate from RiemannProjectivity, reproduced without its stub. -/
def IsProjectiveComplexTorus
    (V : Type*) [NormedAddCommGroup V] [NormedSpace ℂ V]
    (Λ : AddSubgroup V) : Prop :=
  ∃ (n : ℕ) (f : V ⧸ Λ → Projectivization ℂ (Fin (n + 1) → ℂ)),
    Topology.IsClosedEmbedding f ∧
    ∀ z : V, ∃ i : Fin (n + 1),
      AlgebraicGeometry.Foundations.Scheme.ProjectiveCoordinatesIn.Algebraic.ProjectiveCoordinates.InPatch i (f (QuotientAddGroup.mk z)) ∧
      DifferentiableAt ℂ
        (fun w : V => AlgebraicGeometry.Foundations.Scheme.ProjectiveCoordinatesIn.Algebraic.ProjectiveCoordinates.coordinates i (f (QuotientAddGroup.mk w))) z ∧
      Function.Injective (fderiv ℂ
        (fun w : V => AlgebraicGeometry.Foundations.Scheme.ProjectiveCoordinatesIn.Algebraic.ProjectiveCoordinates.coordinates i (f (QuotientAddGroup.mk w))) z)

/-- RiemannProjectivity as a proposition, at the universe needed for subfields of ℂ. -/
def RiemannProjectivityInput : Prop :=
  ∀ (V : Type) [NormedAddCommGroup V] [NormedSpace ℂ V]
    [FiniteDimensional ℂ V] (Λ : AddSubgroup V)
    [DiscreteTopology Λ] [CompactSpace (V ⧸ Λ)],
    IsProjectiveComplexTorus V Λ ↔
      ∃ H : V →ₗ⋆[ℂ] V →ₗ[ℂ] ℂ,
        (∀ u v : V, H v u = star (H u v)) ∧
        (∀ u : V, u ≠ 0 → 0 < (H u u).re) ∧
        (∀ u ∈ Λ, ∀ v ∈ Λ,
          ∃ m : ℤ, (H u v).im = (m : ℝ))

variable {E : Type} [Field E] [NumberField E] [Algebra ℚ E]
  [NumberField.IsCMField E]

/-- Bundle the constructed CM Hermitian form in the sesquilinear type of RiemannProjectivity. -/
def periodHermitianForm (Φ : AlgebraicGeometry.ComplexMultiplication.CM.TypeHodgeStructure.CMEmbeddingType E) :
    AlgebraicGeometry.ComplexMultiplication.CM.PeriodSpace.CMPeriodSpace E →ₗ⋆[ℂ] AlgebraicGeometry.ComplexMultiplication.CM.PeriodSpace.CMPeriodSpace E →ₗ[ℂ] ℂ where
  toFun := Φ.periodHermitian
  map_add' x y := by
    ext z
    exact Φ.periodHermitian_add_left x y z
  map_smul' a x := by
    ext y
    exact AlgebraicGeometry.ComplexMultiplication.CM.PeriodHermitian.cmPeriodHermitian_smul_left E _ a x y

/-- The actual integral trace polarization meets every hypothesis on the
right-hand side of the supplied Riemann criterion. -/
theorem periodHermitianForm_conditions (Φ : AlgebraicGeometry.ComplexMultiplication.CM.TypeHodgeStructure.CMEmbeddingType E) :
    (∀ x y, periodHermitianForm Φ y x = star (periodHermitianForm Φ x y)) ∧
    (∀ x : AlgebraicGeometry.ComplexMultiplication.CM.PeriodSpace.CMPeriodSpace E, x ≠ 0 → 0 < (periodHermitianForm Φ x x).re) ∧
    (∀ x ∈ Φ.periodIntegerLattice.toAddSubgroup,
      ∀ y ∈ Φ.periodIntegerLattice.toAddSubgroup,
        ∃ m : ℤ, (periodHermitianForm Φ x y).im = (m : ℝ)) := by
  refine ⟨Φ.periodHermitian_symm, Φ.periodHermitian_positive, ?_⟩
  intro x hx y hy
  change ∃ m : ℤ, (Φ.periodHermitian x y).im = (m : ℝ)
  rw [Φ.periodHermitian_im]
  obtain ⟨m, hm⟩ := Φ.periodRiemannForm_isInteger x y hx hy
  exact ⟨m, hm.symm⟩

/-- Applying RiemannProjectivity to the constructed full CM lattice gives an actual closed
holomorphic projective embedding with injective derivatives. -/
theorem projective_period_torus
    (hRiemannProjectivity : RiemannProjectivityInput) (Φ : AlgebraicGeometry.ComplexMultiplication.CM.TypeHodgeStructure.CMEmbeddingType E) :
    IsProjectiveComplexTorus (AlgebraicGeometry.ComplexMultiplication.CM.PeriodSpace.CMPeriodSpace E)
      Φ.periodIntegerLattice.toAddSubgroup := by
  let : DiscreteTopology Φ.periodIntegerLattice.toAddSubgroup :=
    Φ.periodIntegerLattice_discrete
  exact (hRiemannProjectivity (AlgebraicGeometry.ComplexMultiplication.CM.PeriodSpace.CMPeriodSpace E) Φ.periodIntegerLattice.toAddSubgroup).mpr
    ⟨periodHermitianForm Φ, periodHermitianForm_conditions Φ⟩

/-- The analytic projectivity statement for the manuscript's odd Galois sign. -/
theorem projective_torus_of_cm_sign
    (hRiemannProjectivity : RiemannProjectivityInput)
    (K : IntermediateField ℚ ℂ) [NumberField K] [IsGalois ℚ K]
    [NumberField.IsCMField K]
    (v : Gal(K/ℚ) → Bool)
    (hv : ∀ τ : Gal(K/ℚ),
      v (AlgebraicGeometry.ComplexMultiplication.GaloisSigns.CM.CMCoefficientField.conjugation K * τ) = !(v τ)) :
    IsProjectiveComplexTorus (AlgebraicGeometry.ComplexMultiplication.CM.PeriodSpace.CMPeriodSpace K)
      (AlgebraicGeometry.ComplexMultiplication.GaloisCMType.CM.CMCoefficientField.embeddingType K ⟨v, hv⟩).periodIntegerLattice.toAddSubgroup :=
  projective_period_torus hRiemannProjectivity _

/-- The embedding supplied by RiemannProjectivity is differentiable with injective derivative
in every standard affine chart containing its value. -/
theorem projective_period_torus_all_charts
    (hRiemannProjectivity : RiemannProjectivityInput) (Φ : AlgebraicGeometry.ComplexMultiplication.CM.TypeHodgeStructure.CMEmbeddingType E) :
    ∃ (n : ℕ) (f : Φ.periodTorus → Projectivization ℂ (Fin (n + 1) → ℂ)),
      Topology.IsClosedEmbedding f ∧
      ∀ (z : AlgebraicGeometry.ComplexMultiplication.CM.PeriodSpace.CMPeriodSpace E) (i : Fin (n + 1)),
        AlgebraicGeometry.Foundations.Scheme.ProjectiveCoordinatesIn.Algebraic.ProjectiveCoordinates.InPatch i (f (QuotientAddGroup.mk z)) →
          DifferentiableAt ℂ
            (fun w => AlgebraicGeometry.ComplexPoints.Analytic.ProjectiveCharts.projectiveFinChart i (f (QuotientAddGroup.mk w))) z ∧
          Function.Injective (fderiv ℂ
            (fun w => AlgebraicGeometry.ComplexPoints.Analytic.ProjectiveCharts.projectiveFinChart i (f (QuotientAddGroup.mk w))) z) := by
  obtain ⟨n, f, hf, hd⟩ := projective_period_torus hRiemannProjectivity Φ
  refine ⟨n, f, hf, ?_⟩
  intro z i hi
  let g : AlgebraicGeometry.ComplexMultiplication.CM.PeriodSpace.CMPeriodSpace E → Projectivization ℂ (Fin (n + 1) → ℂ) :=
    fun w => f (QuotientAddGroup.mk w)
  have hg : ContinuousAt g z := (hf.continuous.comp QuotientAddGroup.continuous_mk).continuousAt
  obtain ⟨j, hj, hdj, hinjj⟩ := hd z
  have hdi := coordinates_differentiableAt_change g hg j i hj hi hdj
  have hinji := coordinates_injective_fderiv_change g hg j i hj hi hdj hinjj
  exact ⟨projectiveFinChart_differentiableAt g i hdi,
    projectiveFinChart_injective_fderiv g hg i hi hdi hinji⟩

end

end OAI.Geometry.ComplexTorus.RiemannProjectivity.Fin.Constructions

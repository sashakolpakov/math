import OAI.ArithmeticGeometry.Descent.CMVariety.IntrinsicHodgeMaps

/-! # Marked Abelian Periods -/

namespace OAI.ArithmeticGeometry.Descent.CMVariety.MarkedAbelianPeriods.IntrinsicPeriods

noncomputable section

section

/-!
Marked periods of actual complex abelian varieties, using a basis of the
kernel of the native exponential. Equal marked period kernels give an
algebraic group isomorphism of the original varieties. Thus the geometric
objects in this comparison are the actual abelian schemes, rather than
an independent category of analytic torus models.
-/

open _root_.CategoryTheory
open OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.AbelianUniformizationEq.Constructions.AbelianUniformization
open scoped BigOperators

variable {ι : Type} [Fintype ι]

/-- An integral basis of the actual exponential lattice is a marking. -/
abbrev Marking (ι : Type) (A : AlgebraicGeometry.ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety) := Module.Basis ι ℤ (AlgebraicGeometry.HodgeConjecture.DegreeTwo.AbelianUniformizationEq.Constructions.AbelianUniformization.periodLattice A)

/-- Markings exist for every actual abelian variety, by the full-lattice theorem. -/
theorem exists_marking (A : AlgebraicGeometry.ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety) : ∃ n : ℕ, Nonempty (Marking (Fin n) A) := by
  let : IsZLattice ℝ (AlgebraicGeometry.HodgeConjecture.DegreeTwo.AbelianUniformizationEq.Constructions.AbelianUniformization.periodLattice A) := AlgebraicGeometry.HodgeConjecture.DegreeTwo.AbelianUniformizationEq.Constructions.AbelianUniformization.periodLattice_full IntrinsicHodgeMaps.Abelian.IntrinsicPeriods.algebraization A
  let : Module.Finite ℤ (AlgebraicGeometry.HodgeConjecture.DegreeTwo.AbelianUniformizationEq.Constructions.AbelianUniformization.periodLattice A) := ZLattice.module_finite ℝ _
  let : Module.Free ℤ (AlgebraicGeometry.HodgeConjecture.DegreeTwo.AbelianUniformizationEq.Constructions.AbelianUniformization.periodLattice A) := ZLattice.module_free ℝ _
  let b := Module.Free.chooseBasis ℤ (AlgebraicGeometry.HodgeConjecture.DegreeTwo.AbelianUniformizationEq.Constructions.AbelianUniformization.periodLattice A)
  exact ⟨Fintype.card (Module.Free.ChooseBasisIndex ℤ (AlgebraicGeometry.HodgeConjecture.DegreeTwo.AbelianUniformizationEq.Constructions.AbelianUniformization.periodLattice A)),
    ⟨b.reindex (Fintype.equivFin _)⟩⟩

/-- Complex-linear extension of the marked period vectors. -/
def periodMap {A : AlgebraicGeometry.ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety} (b : Marking ι A) :
    (ι → ℂ) →ₗ[ℂ] AlgebraicGeometry.HodgeConjecture.DegreeTwo.Transport.Constructions.AbelianModel A :=
  (Pi.basisFun ℂ ι).constr ℂ (fun i => (b i : AlgebraicGeometry.HodgeConjecture.DegreeTwo.Transport.Constructions.AbelianModel A))

theorem periodMap_apply {A : AlgebraicGeometry.ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety} (b : Marking ι A) (v : ι → ℂ) :
    periodMap b v = ∑ i, v i • (b i : AlgebraicGeometry.HodgeConjecture.DegreeTwo.Transport.Constructions.AbelianModel A) := by
  simp [periodMap, Module.Basis.constr_apply_fintype]

/-- The period map agrees with the original marked lattice on integers. -/
theorem periodMap_repr {A : AlgebraicGeometry.ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety} (b : Marking ι A) (l : AlgebraicGeometry.HodgeConjecture.DegreeTwo.AbelianUniformizationEq.Constructions.AbelianUniformization.periodLattice A) :
    periodMap b (fun i => (b.repr l i : ℂ)) = (l : AlgebraicGeometry.HodgeConjecture.DegreeTwo.Transport.Constructions.AbelianModel A) := by
  rw [periodMap_apply]
  have h := congrArg (fun x : AlgebraicGeometry.HodgeConjecture.DegreeTwo.AbelianUniformizationEq.Constructions.AbelianUniformization.periodLattice A => (x : AlgebraicGeometry.HodgeConjecture.DegreeTwo.Transport.Constructions.AbelianModel A)) (b.sum_repr l)
  simpa only [Submodule.coe_sum, Submodule.coe_smul, Int.cast_smul_eq_zsmul] using h

theorem periodMap_integer_mem {A : AlgebraicGeometry.ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety} (b : Marking ι A) (v : ι → ℤ) :
    periodMap b (fun i => (v i : ℂ)) ∈ AlgebraicGeometry.HodgeConjecture.DegreeTwo.AbelianUniformizationEq.Constructions.AbelianUniformization.periodLattice A := by
  rw [periodMap_apply]
  apply Submodule.sum_mem
  intro i _
  rw [Int.cast_smul_eq_zsmul]
  exact Submodule.smul_mem _ _ (b i).property

/-- Fullness of the actual period lattice proves surjectivity. -/
theorem periodMap_surjective {A : AlgebraicGeometry.ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety} (b : Marking ι A) :
    Function.Surjective (periodMap b) := by
  apply LinearMap.range_eq_top.mp
  apply top_unique
  have hspan : Submodule.span ℂ (AlgebraicGeometry.HodgeConjecture.DegreeTwo.AbelianUniformizationEq.Constructions.AbelianUniformization.periodLattice A : Set (AlgebraicGeometry.HodgeConjecture.DegreeTwo.Transport.Constructions.AbelianModel A)) = ⊤ :=
    (IntrinsicHodgeMaps.Abelian.IntrinsicPeriods.torus A).complex_span
  rw [← hspan]
  apply Submodule.span_le.mpr
  intro x hx
  exact ⟨fun i => (b.repr ⟨x, hx⟩ i : ℂ), periodMap_repr b ⟨x, hx⟩⟩

section LinearComparison

variable {V X Y : Type*} [AddCommGroup V] [Module ℂ V]
  [AddCommGroup X] [Module ℂ X] [AddCommGroup Y] [Module ℂ Y]

/-- Equal kernels of surjective linear maps produce the comparison,
with its exact commutative square, by passage to the quotient. -/
theorem exists_linearEquiv_of_eq_ker
    (p : V →ₗ[ℂ] X) (q : V →ₗ[ℂ] Y)
    (hp : Function.Surjective p) (hq : Function.Surjective q) (hker : p.ker = q.ker) :
    ∃ e : X ≃ₗ[ℂ] Y, ∀ v, e (p v) = q v := by
  let f := (p.ker.liftQ q hker.le).comp (p.quotKerEquivOfSurjective hp).symm.toLinearMap
  have hf (v : V) : f (p v) = q v := by
    simp only [f, LinearMap.comp_apply, LinearEquiv.coe_coe,
      LinearMap.quotKerEquivOfSurjective_symm_apply, Submodule.liftQ_apply]
  have hi : Function.Injective f := by
    apply LinearMap.ker_eq_bot.mp
    apply LinearMap.ker_eq_bot'.mpr
    intro x hx
    obtain ⟨v, rfl⟩ := hp x
    have hv : v ∈ q.ker := (hf v).symm.trans hx
    rw [← hker] at hv
    exact hv
  have hs : Function.Surjective f := by
    intro y
    obtain ⟨v, rfl⟩ := hq y
    exact ⟨p v, hf v⟩
  exact ⟨LinearEquiv.ofBijective f ⟨hi, hs⟩, hf⟩

end LinearComparison

/-- Equality of actual marked period kernels gives an algebraic group
isomorphism, with the precise equality on every complex period vector. -/
theorem algebraic_iso_of_marked_period_eq (A B : AlgebraicGeometry.ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety)
    (a : Marking ι A) (b : Marking ι B)
    (hperiod : (periodMap a).ker = (periodMap b).ker) :
    ∃ e : A.toOver ≅ B.toOver, IsMonHom e.hom ∧
      ∀ z : ι → ℂ,
        AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map e.hom
          (AlgebraicGeometry.HodgeConjecture.DegreeTwo.AbelianUniformizationEq.Constructions.AbelianUniformization.periodHomeomorph IntrinsicHodgeMaps.Abelian.IntrinsicPeriods.algebraization A ((IntrinsicHodgeMaps.Abelian.IntrinsicPeriods.torus A).proj (periodMap a z))) =
            AlgebraicGeometry.HodgeConjecture.DegreeTwo.AbelianUniformizationEq.Constructions.AbelianUniformization.periodHomeomorph IntrinsicHodgeMaps.Abelian.IntrinsicPeriods.algebraization B ((IntrinsicHodgeMaps.Abelian.IntrinsicPeriods.torus B).proj (periodMap b z)) := by
  obtain ⟨f, hf⟩ := exists_linearEquiv_of_eq_ker (periodMap a) (periodMap b)
    (periodMap_surjective a) (periodMap_surjective b) hperiod
  have hl : ∀ v ∈ AlgebraicGeometry.HodgeConjecture.DegreeTwo.AbelianUniformizationEq.Constructions.AbelianUniformization.periodLattice A, f v ∈ AlgebraicGeometry.HodgeConjecture.DegreeTwo.AbelianUniformizationEq.Constructions.AbelianUniformization.periodLattice B := by
    intro v hv
    have hv' : periodMap a (fun i => (a.repr ⟨v, hv⟩ i : ℂ)) = v :=
      periodMap_repr a ⟨v, hv⟩
    rw [← hv', hf]
    exact periodMap_integer_mem b (fun i => a.repr ⟨v, hv⟩ i)
  have hli : ∀ v ∈ AlgebraicGeometry.HodgeConjecture.DegreeTwo.AbelianUniformizationEq.Constructions.AbelianUniformization.periodLattice B, f.symm v ∈ AlgebraicGeometry.HodgeConjecture.DegreeTwo.AbelianUniformizationEq.Constructions.AbelianUniformization.periodLattice A := by
    intro v hv
    have he (z : ι → ℂ) : f.symm (periodMap b z) = periodMap a z := by
      rw [← hf, f.symm_apply_apply]
    have hv' : periodMap b (fun i => (b.repr ⟨v, hv⟩ i : ℂ)) = v :=
      periodMap_repr b ⟨v, hv⟩
    rw [← hv', he]
    exact periodMap_integer_mem a (fun i => b.repr ⟨v, hv⟩ i)
  obtain ⟨e, he, hep⟩ := IntrinsicHodgeMaps.Abelian.IntrinsicPeriods.algebraic_iso_of_lattice_equiv A B f hl hli
  refine ⟨e, he, fun z => ?_⟩
  rw [hep, hf]

end

/-!
The marked native period kernel and the actual holomorphic Betti subspace
determine one another. The comparison is built from integration on the
actual exponential lattice; its normalization is fixed on each marked
lattice vector. Equal marked Hodge subspaces therefore give algebraic
group isomorphisms of the actual abelian varieties.
-/

open _root_.CategoryTheory
open OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.AbelianUniformizationEq.Constructions.AbelianUniformization
open OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.AbelianPeriodsTo.Constructions.AbelianPeriods OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.Periods.Constructions.HodgePeriods

variable {ι : Type} [Fintype ι]

/-- Integration over the marked lattice basis gives complex Betti coordinates. -/
def complexCoordinates {A : AlgebraicGeometry.ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety} (b : Marking ι A) :
    A.variety.complexCohomology 1 ≃ₗ[ℂ] (ι → ℂ) :=
  (AlgebraicGeometry.HodgeConjecture.DegreeTwo.AbelianPeriodsTo.Constructions.AbelianPeriods.complexPeriods IntrinsicHodgeMaps.Abelian.IntrinsicPeriods.algebraization A).trans
    ((addMonoidHomLequivInt ℂ).trans (b.constr ℂ).symm)

omit [Fintype ι] in
theorem complexCoordinates_apply {A : AlgebraicGeometry.ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety} (b : Marking ι A)
    (x : A.variety.complexCohomology 1) (i : ι) :
    complexCoordinates b x i = AlgebraicGeometry.HodgeConjecture.DegreeTwo.AbelianPeriodsTo.Constructions.AbelianPeriods.complexPeriods IntrinsicHodgeMaps.Abelian.IntrinsicPeriods.algebraization A x (b i) := rfl

/-- Regard the marked coordinates as a functional on complexified homology. -/
def markedBetti {A : AlgebraicGeometry.ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety} (b : Marking ι A) :
    A.variety.complexCohomology 1 ≃ₗ[ℂ] Module.Dual ℂ (ι → ℂ) :=
  (complexCoordinates b).trans ((Pi.basisFun ℂ ι).constr ℂ)

theorem markedBetti_basis {A : AlgebraicGeometry.ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety} (b : Marking ι A)
    (x : A.variety.complexCohomology 1) (i : ι) :
    markedBetti b x ((Pi.basisFun ℂ ι) i) = AlgebraicGeometry.HodgeConjecture.DegreeTwo.AbelianPeriodsTo.Constructions.AbelianPeriods.complexPeriods IntrinsicHodgeMaps.Abelian.IntrinsicPeriods.algebraization A x (b i) := by
  change (Pi.basisFun ℂ ι).constr ℂ (complexCoordinates b x) ((Pi.basisFun ℂ ι) i) = _
  rw [Module.Basis.constr_basis, complexCoordinates_apply]

/-- Pure Betti classes are exactly the marked functionals which descend
through the actual complex-linear period map. -/
theorem pure_iff_markedBetti_lifts {A : AlgebraicGeometry.ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety} (b : Marking ι A)
    (x : A.variety.complexCohomology 1) :
    x ∈ A.variety.pureBettiSubspace 1 0 ↔
      ∃ f : AlgebraicGeometry.HodgeConjecture.DegreeTwo.Transport.Constructions.AbelianModel A →ₗ[ℂ] ℂ, markedBetti b x = f.comp (periodMap b) := by
  rw [AlgebraicGeometry.HodgeConjecture.DegreeTwo.Periods.Constructions.HodgePeriods.holomorphic_iff_complexLinear_periods IntrinsicHodgeMaps.Abelian.IntrinsicPeriods.algebraization A]
  constructor
  · rintro ⟨f, hf⟩
    refine ⟨f, (Pi.basisFun ℂ ι).ext fun i => ?_⟩
    rw [markedBetti_basis, LinearMap.comp_apply]
    change AlgebraicGeometry.HodgeConjecture.DegreeTwo.AbelianPeriodsTo.Constructions.AbelianPeriods.complexPeriods IntrinsicHodgeMaps.Abelian.IntrinsicPeriods.algebraization A x (b i) =
      f ((Pi.basisFun ℂ ι).constr ℂ (fun j => (b j : AlgebraicGeometry.HodgeConjecture.DegreeTwo.Transport.Constructions.AbelianModel A)) ((Pi.basisFun ℂ ι) i))
    rw [Module.Basis.constr_basis]
    exact hf (b i)
  · rintro ⟨f, hf⟩
    have he : (AlgebraicGeometry.HodgeConjecture.DegreeTwo.AbelianPeriodsTo.Constructions.AbelianPeriods.complexPeriods IntrinsicHodgeMaps.Abelian.IntrinsicPeriods.algebraization A x).toIntLinearMap =
        (f.restrictScalars ℤ).comp (AlgebraicGeometry.HodgeConjecture.DegreeTwo.AbelianUniformizationEq.Constructions.AbelianUniformization.periodLattice A).subtype := by
      apply b.ext
      intro i
      have hi := LinearMap.congr_fun hf ((Pi.basisFun ℂ ι) i)
      rw [markedBetti_basis, LinearMap.comp_apply] at hi
      change AlgebraicGeometry.HodgeConjecture.DegreeTwo.AbelianPeriodsTo.Constructions.AbelianPeriods.complexPeriods IntrinsicHodgeMaps.Abelian.IntrinsicPeriods.algebraization A x (b i) = f (b i : AlgebraicGeometry.HodgeConjecture.DegreeTwo.Transport.Constructions.AbelianModel A)
      simpa only [periodMap, Module.Basis.constr_basis] using hi
    exact ⟨f, fun l => LinearMap.congr_fun he l⟩

/-- The actual holomorphic Betti space expressed in the marking. -/
def markedHolomorphic {A : AlgebraicGeometry.ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety} (b : Marking ι A) :
    Submodule ℂ (Module.Dual ℂ (ι → ℂ)) :=
  (A.variety.pureBettiSubspace 1 0).map (markedBetti b).toLinearMap

/-- The Hodge subspace is the annihilator of the actual marked period kernel. -/
theorem markedHolomorphic_eq_annihilator {A : AlgebraicGeometry.ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety} (b : Marking ι A) :
    markedHolomorphic b = (periodMap b).ker.dualAnnihilator := by
  rw [← LinearMap.range_dualMap_eq_dualAnnihilator_ker]
  ext φ
  constructor
  · rintro ⟨x, hx, rfl⟩
    obtain ⟨f, hf⟩ := (pure_iff_markedBetti_lifts b x).mp hx
    exact ⟨f, hf.symm⟩
  · rintro ⟨f, rfl⟩
    let x := (markedBetti b).symm ((periodMap b).dualMap f)
    have hx : markedBetti b x = (periodMap b).dualMap f :=
      (markedBetti b).apply_symm_apply _
    exact ⟨x, (pure_iff_markedBetti_lifts b x).mpr ⟨f, hx⟩, hx⟩

theorem period_ker_eq_of_markedHolomorphic_eq (A B : AlgebraicGeometry.ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety)
    (a : Marking ι A) (b : Marking ι B)
    (h : markedHolomorphic a = markedHolomorphic b) :
    (periodMap a).ker = (periodMap b).ker := by
  apply Subspace.dualAnnihilator_inj.mp
  rw [← markedHolomorphic_eq_annihilator a, ← markedHolomorphic_eq_annihilator b]
  exact h

/-- Actual marked holomorphic subspaces classify the abelian varieties
algebraically, with compatibility on the native exponential points. -/
theorem algebraic_iso_of_markedHolomorphic_eq (A B : AlgebraicGeometry.ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety)
    (a : Marking ι A) (b : Marking ι B)
    (h : markedHolomorphic a = markedHolomorphic b) :
    ∃ e : A.toOver ≅ B.toOver, IsMonHom e.hom ∧
      ∀ z : ι → ℂ,
        AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map e.hom
          (AlgebraicGeometry.HodgeConjecture.DegreeTwo.AbelianUniformizationEq.Constructions.AbelianUniformization.periodHomeomorph IntrinsicHodgeMaps.Abelian.IntrinsicPeriods.algebraization A ((IntrinsicHodgeMaps.Abelian.IntrinsicPeriods.torus A).proj (periodMap a z))) =
            AlgebraicGeometry.HodgeConjecture.DegreeTwo.AbelianUniformizationEq.Constructions.AbelianUniformization.periodHomeomorph IntrinsicHodgeMaps.Abelian.IntrinsicPeriods.algebraization B ((IntrinsicHodgeMaps.Abelian.IntrinsicPeriods.torus B).proj (periodMap b z)) :=
  algebraic_iso_of_marked_period_eq A B a b (period_ker_eq_of_markedHolomorphic_eq A B a b h)

end

end OAI.ArithmeticGeometry.Descent.CMVariety.MarkedAbelianPeriods.IntrinsicPeriods

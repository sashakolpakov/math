import OAI.AlgebraicGeometry.Resolution.Blowups.GlobalBoundary.Intersection
import OAI.AlgebraicGeometry.Resolution.Blowups.GlobalControlled.Factorization
import OAI.AlgebraicGeometry.Resolution.Blowups.GlobalBlowup.Nonzero
import OAI.AlgebraicGeometry.Resolution.Blowups.Coordinate.BoundaryTransform

/-! # Mixed Boundary -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups.Global.MixedBoundary.Construction

noncomputable section

/-! Exact native global boundary transforms with one new exceptional label at every blowup. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u v

def boundaryMonomialSheaf {X : Scheme.{u}} {ι : Type v} [Fintype ι]
    (D : ι → X.IdealSheafData) (a : ι → ℕ) : X.IdealSheafData := ∏ j, D j ^ a j

theorem idealSheaf_finset_prod_ideal {X : Scheme.{u}} {ι : Type v}
    (D : ι → X.IdealSheafData) (S : Finset ι) (U : X.affineOpens) :
    (∏ j ∈ S, D j).ideal U = ∏ j ∈ S, (D j).ideal U := by
  classical
  induction S using Finset.induction_on with
  | empty =>
      simp only [Finset.prod_empty, Scheme.IdealSheafData.one_eq_top,
        Scheme.IdealSheafData.ideal_top, Pi.top_apply, Ideal.one_eq_top]
  | @insert j S hj ih =>
      rw [Finset.prod_insert hj, Scheme.IdealSheafData.ideal_mul, Pi.mul_apply, ih,
        Finset.prod_insert hj]

theorem boundaryMonomialSheaf_ideal {X : Scheme.{u}} {ι : Type v} [Fintype ι]
    (D : ι → X.IdealSheafData) (a : ι → ℕ) (U : X.affineOpens) :
    (boundaryMonomialSheaf D a).ideal U = ∏ j, (D j).ideal U ^ a j := by
  rw [boundaryMonomialSheaf, idealSheaf_finset_prod_ideal]
  rfl

theorem idealSheaf_comap_finset_prod_open {X Y : Scheme.{u}} {ι : Type v}
    (D : ι → Y.IdealSheafData) (S : Finset ι) (f : X ⟶ Y) [IsOpenImmersion f] :
    (∏ j ∈ S, D j).comap f = ∏ j ∈ S, (D j).comap f := by
  classical
  induction S using Finset.induction_on with
  | empty =>
      simp only [Finset.prod_empty]
      exact Scheme.IdealSheafData.comap_top f
  | @insert j S hj ih => rw [Finset.prod_insert hj, IdealSheaf.ProductRestriction.Construction.idealSheaf_comap_mul_open, ih, Finset.prod_insert hj]

theorem boundaryMonomialSheaf_comap_open {X Y : Scheme.{u}} {ι : Type v} [Fintype ι]
    (D : ι → Y.IdealSheafData) (a : ι → ℕ) (f : X ⟶ Y) [IsOpenImmersion f] :
    (boundaryMonomialSheaf D a).comap f = boundaryMonomialSheaf (fun j => (D j).comap f) a := by
  rw [boundaryMonomialSheaf, idealSheaf_comap_finset_prod_open]
  simp only [IdealSheaf.ColonRestriction.Construction.idealSheaf_comap_pow_open, boundaryMonomialSheaf]

theorem affineQuotientKernel_finset_prod {R : Type u} [CommRing R] {ι : Type v}
    (D : ι → Ideal R) (S : Finset ι) :
    Affine.QuotientKernel.Construction.affineQuotientKernel (∏ j ∈ S, D j) = ∏ j ∈ S, Affine.QuotientKernel.Construction.affineQuotientKernel (D j) := by
  classical
  induction S using Finset.induction_on with
  | empty =>
      simp only [Finset.prod_empty, Ideal.one_eq_top, Scheme.IdealSheafData.one_eq_top]
      exact DifferentialUnitGluing.Construction.affineQuotientKernel_top (R := R)
  | @insert j S hj ih => rw [Finset.prod_insert hj, IdealSheaf.ProductRestriction.Construction.affineQuotientKernel_mul, ih, Finset.prod_insert hj]

theorem ideal_span_finset_prod {R : Type u} [CommRing R] {ι : Type v}
    (w : ι → R) (S : Finset ι) : Ideal.span {∏ j ∈ S, w j} = ∏ j ∈ S, Ideal.span {w j} := by
  classical
  induction S using Finset.induction_on with
  | empty => simp only [Finset.prod_empty, Ideal.span_singleton_one, Ideal.one_eq_top]
  | @insert j S hj ih =>
      rw [Finset.prod_insert hj, ← Ideal.span_singleton_mul_span_singleton, ih, Finset.prod_insert hj]

theorem boundaryMonomialSheaf_affineQuotientKernel
    {R : Type u} [CommRing R] {ι : Type v} [Fintype ι] (w : ι → R) (a : ι → ℕ) :
    boundaryMonomialSheaf (fun j => Affine.QuotientKernel.Construction.affineQuotientKernel (Ideal.span {w j})) a =
      Affine.QuotientKernel.Construction.affineQuotientKernel (Ideal.span {LabelledBoundaryMonomialTransform.Construction.boundaryMonomialElement w a}) := by
  rw [boundaryMonomialSheaf, LabelledBoundaryMonomialTransform.Construction.boundaryMonomialElement, ideal_span_finset_prod, affineQuotientKernel_finset_prod]
  apply Finset.prod_congr rfl
  intro j _
  rw [← Ideal.span_singleton_pow, Affine.QuotientKernel.Construction.affineQuotientKernel_pow]

theorem boundaryMonomialSheaf_local_equations {X : Scheme.{u}} {ι : Type v} [Fintype ι]
    (D : ι → X.IdealSheafData) (a : ι → ℕ) (U : X.affineOpens)
    (w : ι → Γ(X, U)) (hw : ∀ j, (D j).ideal U = Ideal.span {w j}) :
    (boundaryMonomialSheaf D a).ideal U = Ideal.span {LabelledBoundaryMonomialTransform.Construction.boundaryMonomialElement w a} := by
  rw [boundaryMonomialSheaf_ideal, LabelledBoundaryMonomialTransform.Construction.boundaryMonomialElement, ideal_span_finset_prod]
  simp only [hw, Ideal.span_singleton_pow]

variable {X : Scheme.{u}} [IsIntegral X] [IsLocallyNoetherian X]

def globalBlowupMixedBoundary (I : X.IdealSheafData) (hI : I ≠ ⊥) {ι : Type v}
    (D : ι → X.IdealSheafData) (C : Finset ι) : Option ι → (GlobalBlowup.Data.Construction.globalBlowup I hI).IdealSheafData := by
  classical
  exact fun j => match j with
    | none => I.comap (GlobalBlowup.Data.Construction.globalBlowupToBase I hI)
    | some l => if l ∈ C then GlobalControlled.Ideal.Construction.globalBlowupControlledIdeal I (D l) hI 1
      else (D l).comap (GlobalBlowup.Data.Construction.globalBlowupToBase I hI)

theorem globalBlowupMixedBoundary_ne_bot (I : X.IdealSheafData) (hI : I ≠ ⊥) {ι : Type v}
    (D : ι → X.IdealSheafData) (C : Finset ι) (hD : ∀ j, D j ≠ ⊥) :
    ∀ j, globalBlowupMixedBoundary I hI D C j ≠ ⊥ := by
  classical
  intro j
  cases j with
  | none => exact GlobalBlowup.Nonzero.Construction.globalBlowup_totalIdeal_ne_bot I I hI hI
  | some j =>
      by_cases hj : j ∈ C
      · simpa only [globalBlowupMixedBoundary, ite_eq_left hj] using
          GlobalBlowup.Nonzero.Construction.globalBlowupControlledIdeal_ne_bot I (D j) hI 1 (hD j)
      · simpa only [globalBlowupMixedBoundary, ite_eq_right hj] using
          GlobalBlowup.Nonzero.Construction.globalBlowup_totalIdeal_ne_bot I (D j) hI (hD j)

theorem globalBlowupMixedBoundary_comap_reesChart
    (I : X.IdealSheafData) (hI : I ≠ ⊥) {ι : Type v}
    (D : ι → X.IdealSheafData) (C : Finset ι) (U : X.affineOpens)
    (w : ι → Γ(X, U)) (hD : ∀ j, (D j).ideal U = Ideal.span {w j})
    (hw : ∀ j ∈ C, w j ∈ I.ideal U) (d : I.ideal U) (j : Option ι) :
    (globalBlowupMixedBoundary I hI D C j).comap (GlobalControlled.Chart.Construction.globalBlowupReesChart I hI U d) =
      Affine.QuotientKernel.Construction.affineQuotientKernel (Ideal.span {MixedBoundary.Equations.Construction.blowupMixedBoundaryFamily (I.ideal U) d C w hw j}) := by
  classical
  cases j with
  | none =>
      rw [globalBlowupMixedBoundary, GlobalControlled.Factorization.Construction.totalIdeal_comap_globalBlowupReesChart, ExceptionalIdeal.Construction.blowupChart_extendedIdeal]
      rfl
  | some j =>
      by_cases hj : j ∈ C
      · rw [globalBlowupMixedBoundary, ite_eq_left hj, GlobalControlled.Chart.Construction.globalBlowupControlledIdeal_comap_reesChart, hD j,
          MixedBoundary.Equations.Construction.blowupMixedBoundaryFamily, dite_eq_left hj]
        exact congrArg Affine.QuotientKernel.Construction.affineQuotientKernel
          (Coordinate.BoundaryTransform.Construction.blowup_principal_coordinate_controlledTransform (I.ideal U) d ⟨w j, hw j hj⟩)
      · rw [globalBlowupMixedBoundary, ite_eq_right hj, GlobalControlled.Factorization.Construction.totalIdeal_comap_globalBlowupReesChart, hD j,
          Ideal.map_span, Set.image_singleton, MixedBoundary.Equations.Construction.blowupMixedBoundaryFamily, dite_eq_right hj]

theorem global_boundary_monomial_transform_on_chart
    (I : X.IdealSheafData) (hI : I ≠ ⊥) {ι : Type u} [Fintype ι]
    (D : ι → X.IdealSheafData) (C : Finset ι) (a : ι → ℕ) (b : ℕ)
    (hb : b ≤ Boundary.MonomialSchedule.Construction.boundaryFaceWeight a C) (U : X.affineOpens)
    (w : ι → Γ(X, U)) (hD : ∀ j, (D j).ideal U = Ideal.span {w j})
    (hw : ∀ j ∈ C, w j ∈ I.ideal U) (d : I.ideal U) :
    (GlobalControlled.Ideal.Construction.globalBlowupControlledIdeal I (boundaryMonomialSheaf D a) hI b).comap
        (GlobalControlled.Chart.Construction.globalBlowupReesChart I hI U d) =
      (boundaryMonomialSheaf (globalBlowupMixedBoundary I hI D C)
        (Boundary.MonomialSchedule.Construction.boundaryScheduleExponents a b C)).comap (GlobalControlled.Chart.Construction.globalBlowupReesChart I hI U d) := by
  classical
  rw [GlobalControlled.Chart.Construction.globalBlowupControlledIdeal_comap_reesChart, boundaryMonomialSheaf_local_equations D a U w hD,
    boundaryMonomialSheaf_comap_open]
  simp_rw [globalBlowupMixedBoundary_comap_reesChart I hI D C U w hD hw d]
  rw [boundaryMonomialSheaf_affineQuotientKernel]
  exact congrArg Affine.QuotientKernel.Construction.affineQuotientKernel
    (LabelledBoundaryMonomialTransform.Construction.boundaryMonomialElement_controlledTransform (I.ideal U) d C w hw a b hb)

end

end OAI.AlgebraicGeometry.Resolution.Blowups.Global.MixedBoundary.Construction

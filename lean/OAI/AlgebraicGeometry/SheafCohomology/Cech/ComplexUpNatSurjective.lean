/-
Derived from AINTLIB:
  projects/ModularCurves/ModularCurves/ForMathlib/TotalComplexUpNatHorizontalEdgeHigher.lean
The upstream AINTLIB repository is licensed under Apache 2.0.
This file has been modified.
-/
import OAI.AlgebraicGeometry.SheafCohomology.Cech.ComplexUpNatRow
import OAI.AlgebraicGeometry.SheafCohomology.Cech.PositiveCycleHomology

/-! # Complex Up Nat Surjective -/

namespace OAI.AlgebraicGeometry.SheafCohomology.Cech.ComplexUpNatSurjective.Projective

noncomputable section

/-! Surjectivity of the horizontal edge on homology in every positive degree. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits

open OAI.AlgebraicGeometry.SheafCohomology.Cech.PositiveCycleHomology.Projective.CycleHomology

universe u

variable (K : HomologicalComplex₂ AddCommGrpCat.{u} (.up ℕ) (.up ℕ))
    [K.HasTotal (.up ℕ)]

/-- Exact augmented rows make the horizontal edge map surjective on every
positive-degree homology group of the genuine total complex. -/
theorem horizontal_edge_homology_surjective
    (A : CochainComplex AddCommGrpCat.{u} ℕ)
    (e : ∀ q, A.X q ⟶ (K.X q).X 0)
    (he : ∀ q q', (ComplexShape.up ℕ).Rel q q' →
      e q ≫ (K.d q q').f 0 = A.d q q' ≫ e q')
    (w : ∀ q, e q ≫ (K.X q).d 0 1 = 0)
    (haug : ∀ q, (ShortComplex.mk (e q) ((K.X q).d 0 1) (w q)).Exact)
    (hmono : ∀ q, Mono (e q)) (hrows : ComplexUpNatNormalize.Projective.RowsExact K) (n : ℕ) :
    Function.Surjective (HomologicalComplex.homologyMap
      ((UpNatHorizontalEdge.HomologicalComplex₂.totalUpNatHorizontalEdge K) A e he w) (n + 1)) := by
  let T := K.total (.up ℕ)
  let edge := (UpNatHorizontalEdge.HomologicalComplex₂.totalUpNatHorizontalEdge K) A e he w
  intro ξ
  have hπ : Function.Surjective (T.homologyπ (n + 1)) :=
    (AddCommGrpCat.epi_iff_surjective (T.homologyπ (n + 1))).mp inferInstance
  obtain ⟨xc, rfl⟩ := hπ ξ
  let x : T.X (n + 1) := T.iCycles (n + 1) xc
  have hx : T.d (n + 1) (n + 2) x = 0 := by
    have h := congrArg (fun g => g xc) (T.iCycles_d (n + 1) (n + 2))
    simpa only [x, ConcreteCategory.comp_apply, AddCommGrpCat.hom_zero,
      AddMonoidHom.zero_apply] using h
  obtain ⟨a, ha, z, haz⟩ := ComplexUpNatRow.Projective.exists_horizontal_cycle_lift K A e he w haug hmono hrows n x hx
  have hedgeCycle : T.d (n + 1) (n + 2) (edge.f (n + 1) a) = 0 := by
    have h := congrArg (fun g => g a) (edge.comm (n + 1) (n + 2))
    simpa only [ConcreteCategory.comp_apply, ha, map_zero] using h
  have hdiff : x - edge.f (n + 1) a = T.d n (n + 1) z := by
    change x - ((UpNatHorizontalEdge.HomologicalComplex₂.totalUpNatHorizontalEdge K) A e he w).f (n + 1) a = _
    rw [haz]
    abel
  have hxc : PositiveCycleHomology.Projective.CycleHomology.abCyclesMk n T x hx = xc := by
    apply (AddCommGrpCat.mono_iff_injective (T.iCycles (n + 1))).mp inferInstance
    simp only [PositiveCycleHomology.Projective.CycleHomology.i_abCyclesMk, x]
  refine ⟨A.homologyπ (n + 1) (PositiveCycleHomology.Projective.CycleHomology.abCyclesMk n A a ha), ?_⟩
  calc
    HomologicalComplex.homologyMap edge (n + 1)
        (A.homologyπ (n + 1) (PositiveCycleHomology.Projective.CycleHomology.abCyclesMk n A a ha)) =
        T.homologyπ (n + 1) (PositiveCycleHomology.Projective.CycleHomology.abCyclesMk n T (edge.f (n + 1) a) hedgeCycle) :=
      PositiveCycleHomology.Projective.CycleHomology.homologyMap_abCyclesMk n edge a ha hedgeCycle
    _ = T.homologyπ (n + 1) (PositiveCycleHomology.Projective.CycleHomology.abCyclesMk n T x hx) :=
      (PositiveCycleHomology.Projective.CycleHomology.homologyπ_cyclesMk_eq_of_sub_eq_boundary n T x (edge.f (n + 1) a) hx
        hedgeCycle z hdiff).symm
    _ = T.homologyπ (n + 1) xc := by rw [hxc]

end

end OAI.AlgebraicGeometry.SheafCohomology.Cech.ComplexUpNatSurjective.Projective

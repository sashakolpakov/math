/-
Derived from AINTLIB:
  projects/ModularCurves/ModularCurves/ForMathlib/TotalComplexUpNatHorizontalEdgeHOne.lean
The upstream AINTLIB repository is licensed under Apache 2.0.
This file has been modified.
-/
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.TotalComplex.BoundaryLifting
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.TotalComplex.HomologySurjectivity

/-! # Homology Comparison -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.TotalComplex.HomologyComparison

noncomputable section

/-! The augmented-row comparison is a quasi-isomorphism in every positive degree. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits

universe u

variable (K : HomologicalComplex₂ AddCommGrpCat.{u} (.up ℕ) (.up ℕ))
    [K.HasTotal (.up ℕ)]

/-- The horizontal edge map is injective on homology in every positive degree. -/
theorem horizontal_edge_homology_injective
    (A : CochainComplex AddCommGrpCat.{u} ℕ)
    (e : ∀ q, A.X q ⟶ (K.X q).X 0)
    (he : ∀ q q', (ComplexShape.up ℕ).Rel q q' →
      e q ≫ (K.d q q').f 0 = A.d q q' ≫ e q')
    (w : ∀ q, e q ≫ (K.X q).d 0 1 = 0)
    (haug : ∀ q, (ShortComplex.mk (e q) ((K.X q).d 0 1) (w q)).Exact)
    (hmono : ∀ q, Mono (e q)) (hrows : CycleNormalization.RowsExact K) (n : ℕ) :
    Function.Injective (HomologicalComplex.homologyMap
      (HorizontalEdge.totalUpNatHorizontalEdge K A e he w) (n + 1)) := by
  let T := K.total (.up ℕ)
  let edge := HorizontalEdge.totalUpNatHorizontalEdge K A e he w
  intro ξ η hξη
  rw [← sub_eq_zero]
  have hmapzero : HomologicalComplex.homologyMap edge (n + 1) (ξ - η) = 0 := by
    rw [map_sub, hξη, sub_self]
  have hπ : Function.Surjective (A.homologyπ (n + 1)) :=
    (AddCommGrpCat.epi_iff_surjective (A.homologyπ (n + 1))).mp inferInstance
  obtain ⟨ac, hac⟩ := hπ (ξ - η)
  let a : A.X (n + 1) := A.iCycles (n + 1) ac
  have haCycle : A.d (n + 1) (n + 2) a = 0 := by
    have h := congrArg (fun g => g ac) (A.iCycles_d (n + 1) (n + 2))
    simpa only [a, ConcreteCategory.comp_apply, AddCommGrpCat.hom_zero,
      AddMonoidHom.zero_apply] using h
  have hedgeCycle : T.d (n + 1) (n + 2) (edge.f (n + 1) a) = 0 := by
    have h := congrArg (fun g => g a) (edge.comm (n + 1) (n + 2))
    simpa only [ConcreteCategory.comp_apply, haCycle, map_zero] using h
  have hac' : Positive.PositiveCycleHomology.TotalComplex.CycleHomology.abCyclesMk n A a haCycle = ac := by
    apply (AddCommGrpCat.mono_iff_injective (A.iCycles (n + 1))).mp inferInstance
    simp only [Positive.PositiveCycleHomology.TotalComplex.CycleHomology.i_abCyclesMk, a]
  have hedgeClassZero :
      T.homologyπ (n + 1) (Positive.PositiveCycleHomology.TotalComplex.CycleHomology.abCyclesMk n T (edge.f (n + 1) a) hedgeCycle) = 0 := by
    calc
      _ = HomologicalComplex.homologyMap edge (n + 1)
          (A.homologyπ (n + 1) (Positive.PositiveCycleHomology.TotalComplex.CycleHomology.abCyclesMk n A a haCycle)) :=
        (Positive.PositiveCycleHomology.TotalComplex.CycleHomology.homologyMap_abCyclesMk n edge a haCycle hedgeCycle).symm
      _ = HomologicalComplex.homologyMap edge (n + 1) (ξ - η) := by rw [hac', hac]
      _ = 0 := hmapzero
  obtain ⟨z, hz⟩ := Positive.PositiveCycleHomology.TotalComplex.CycleHomology.exists_boundary_of_homologyπ_abCyclesMk_eq_zero n T
    (edge.f (n + 1) a) hedgeCycle hedgeClassZero
  obtain ⟨b, hb⟩ := BoundaryLifting.exists_horizontal_boundary_lift K A e he w haug hmono hrows n a z hz
  have hzeroCycle : A.d (n + 1) (n + 2) (0 : A.X (n + 1)) = 0 := by simp
  have habZero : Positive.PositiveCycleHomology.TotalComplex.CycleHomology.abCyclesMk n A 0 hzeroCycle = 0 := by
    apply (AddCommGrpCat.mono_iff_injective (A.iCycles (n + 1))).mp inferInstance
    simp only [Positive.PositiveCycleHomology.TotalComplex.CycleHomology.i_abCyclesMk, map_zero]
  have haClassZero : A.homologyπ (n + 1) (Positive.PositiveCycleHomology.TotalComplex.CycleHomology.abCyclesMk n A a haCycle) = 0 := by
    calc
      _ = A.homologyπ (n + 1) (Positive.PositiveCycleHomology.TotalComplex.CycleHomology.abCyclesMk n A 0 hzeroCycle) :=
        Positive.PositiveCycleHomology.TotalComplex.CycleHomology.homologyπ_cyclesMk_eq_of_sub_eq_boundary n A a 0 haCycle hzeroCycle b
          (by simpa only [sub_zero] using hb.symm)
      _ = 0 := by rw [habZero, map_zero]
  calc
    ξ - η = A.homologyπ (n + 1) ac := hac.symm
    _ = A.homologyπ (n + 1) (Positive.PositiveCycleHomology.TotalComplex.CycleHomology.abCyclesMk n A a haCycle) := by rw [hac']
    _ = 0 := haClassZero

/-- Exact augmented rows give the actual homology comparison in all positive degrees. -/
theorem horizontal_edge_quasiIsoAt
    (A : CochainComplex AddCommGrpCat.{u} ℕ)
    (e : ∀ q, A.X q ⟶ (K.X q).X 0)
    (he : ∀ q q', (ComplexShape.up ℕ).Rel q q' →
      e q ≫ (K.d q q').f 0 = A.d q q' ≫ e q')
    (w : ∀ q, e q ≫ (K.X q).d 0 1 = 0)
    (haug : ∀ q, (ShortComplex.mk (e q) ((K.X q).d 0 1) (w q)).Exact)
    (hmono : ∀ q, Mono (e q)) (hrows : CycleNormalization.RowsExact K) (n : ℕ) :
    QuasiIsoAt (HorizontalEdge.totalUpNatHorizontalEdge K A e he w) (n + 1) := by
  rw [quasiIsoAt_iff_isIso_homologyMap]
  let f := HomologicalComplex.homologyMap (HorizontalEdge.totalUpNatHorizontalEdge K A e he w) (n + 1)
  have : Mono f := (AddCommGrpCat.mono_iff_injective f).mpr
    (horizontal_edge_homology_injective K A e he w haug hmono hrows n)
  have : Epi f := (AddCommGrpCat.epi_iff_surjective f).mpr
    (HomologySurjectivity.horizontal_edge_homology_surjective K A e he w haug hmono hrows n)
  exact isIso_of_mono_of_epi f

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.TotalComplex.HomologyComparison

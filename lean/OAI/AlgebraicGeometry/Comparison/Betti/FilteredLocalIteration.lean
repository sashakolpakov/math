import OAI.AlgebraicGeometry.Comparison.Betti.LowestTypeDolbeaultClosed
import OAI.AlgebraicGeometry.Comparison.Betti.ManifoldDolbeaultPoincare

/-! # Filtered Local Iteration -/

namespace OAI.AlgebraicGeometry.Comparison.Betti.FilteredLocalIteration.Hodge

noncomputable section

section

/-! An actual local Dolbeault primitive removes the lowest allowed type
of a closed filtered de Rham form and raises its filtration by one. -/

open _root_.TopologicalSpace
open scoped _root_.Manifold ContDiff

attribute [local instance] Analysis.DifferentialForms.Manifold.ComplexCharts.complexManifold_isRealSmooth

variable {E M : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedSpace ℂ E]
  [IsScalarTower ℝ ℂ E] [FiniteDimensional ℂ E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℂ, E) ∞ M]

theorem exists_local_filtered_correction (U : Opens M) (n p q : ℕ) (hn : n = p + q)
    (a : Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm E U (n + 1)) (ha : a ∈ Open.FiltrationDescent.Hodge.openFormFiltration U (n + 1) (p : ℤ))
    (hd : Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm.d a = 0) (x : U) :
    ∃ V : Opens M, x.val ∈ V ∧ ∃ hV : V ≤ U,
      ∃ u : Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm E V n, ∃ c : Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm E V (n + 1),
        DivisorClass.Chern.Open.ManifoldBidegree.OpenManifoldHasBidegree p q u ∧ Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm.d c = 0 ∧
        c ∈ Open.FiltrationDescent.Hodge.openFormFiltration V (n + 1) ((p : ℤ) + 1) ∧
        c + Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm.d u = Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm.restrict hV a := by
  have : FiniteDimensional ℝ E := FiniteDimensional.trans ℝ ℂ E
  let j : Analysis.HodgeTheory.Decomposition.Core.Constructions.Bidegree n := ⟨(p, q), hn.symm⟩
  let i := Analysis.HodgeTheory.Decomposition.Dolbeault.Constructions.advanceAntiholomorphic j
  let b := Open.FiltrationDescent.Hodge.openTypeProjection U (n + 1) i a
  have hb : DivisorClass.Chern.Open.ManifoldBidegree.OpenManifoldHasBidegree p (q + 1) b :=
    (Open.ChartEvaluation.Hodge.mem_openPureFormsInDegree_iff U (n + 1) i b).mp (Open.ChartEvaluation.Hodge.openTypeProjection_pure U (n + 1) i a)
  have hdb : DivisorClass.Chern.Open.ManifoldDolbeault.openManifoldDolbeaultD p (q + 1) (n + 1) b = 0 :=
    LowestTypeDolbeaultClosed.Hodge.lowestType_dolbeault_closed U (n + 1) i a ha hd
  obtain ⟨V, hxV, hV, u, hup, hu⟩ :=
    ManifoldDolbeaultPoincare.manifoldLocalDolbeaultPoincare U n p q hn b hdb hb x
  have huj : u ∈ Open.ChartEvaluation.Hodge.openPureFormsInDegree V n j := (Open.ChartEvaluation.Hodge.mem_openPureFormsInDegree_iff V n j u).mpr hup
  have huf : u ∈ Open.FiltrationDescent.Hodge.openFormFiltration V n (p : ℤ) :=
    Open.ChartEvaluation.Hodge.openPureFormsInDegree_mem_filtration V n j _ le_rfl u huj
  let ar := Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm.restrict hV a
  let c := ar + (-1 : ℂ) • Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm.d u
  have hcf : c ∈ Open.FiltrationDescent.Hodge.openFormFiltration V (n + 1) (p : ℤ) :=
    Submodule.add_mem _ (Open.FiltrationDescent.Hodge.openFormFiltration_restrict hV (n + 1) _ a ha)
      (Submodule.smul_mem _ _ (Open.FiltrationDescent.Hodge.openFormFiltration_d n _ u huf))
  have hci : Open.FiltrationDescent.Hodge.openTypeProjection V (n + 1) i c = 0 := by
    change Open.FiltrationDescent.Hodge.openTypeProjection V (n + 1) i (ar + (-1 : ℂ) • Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm.d u) = 0
    rw [map_add, map_smul, Open.PureDifferential.Hodge.openTypeProjection_d_doublePrime V n j u huj]
    change Open.FiltrationDescent.Hodge.openTypeProjection V (n + 1) i (Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm.restrict hV a) +
      (-1 : ℂ) • DivisorClass.Chern.Open.ManifoldDolbeault.openManifoldDolbeaultD p q n u = 0
    rw [← Open.FiltrationDescent.Hodge.openTypeProjection_restrict hV (n + 1) i a, hu]
    apply Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm.ext
    intro y
    ext v
    change Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm.restrict hV b y v +
      (-1 : ℂ) * Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm.restrict hV b y v = 0
    ring
  have hcd : Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm.d c = 0 := by
    change Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm.d (ar + (-1 : ℂ) • Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm.d u) = 0
    rw [map_add, map_smul, Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm.d_squared, smul_zero, add_zero]
    change Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm.d (Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm.restrict hV a) = 0
    rw [← Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm.restrict_d, hd, map_zero]
  refine ⟨V, hxV, hV, u, c, hup, hcd, Open.FiltrationStep.Hodge.openFormFiltration_raise V (n + 1) i c hcf hci, ?_⟩
  apply Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm.ext
  intro y
  ext v
  change (ar y v + (-1 : ℂ) * Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm.d u y v) +
    Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm.d u y v = ar y v
  ring

end

/-! Finite iteration of actual local Dolbeault corrections raises the
smooth filtration while retaining a primitive in the initial filtration. -/

open _root_.TopologicalSpace
open scoped _root_.Manifold ContDiff

attribute [local instance] Analysis.DifferentialForms.Manifold.ComplexCharts.complexManifold_isRealSmooth

variable {E M : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedSpace ℂ E]
  [IsScalarTower ℝ ℂ E] [FiniteDimensional ℂ E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℂ, E) ∞ M]

omit [FiniteDimensional ℂ E] in
theorem openPure_mem_filtration (U : Opens M) (n p q : ℕ) (hn : n = p + q)
    (r : ℤ) (hr : r ≤ (p : ℤ)) (a : Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm E U n)
    (ha : DivisorClass.Chern.Open.ManifoldBidegree.OpenManifoldHasBidegree p q a) : a ∈ Open.FiltrationDescent.Hodge.openFormFiltration U n r := by
  let i : Analysis.HodgeTheory.Decomposition.Core.Constructions.Bidegree n := ⟨(p, q), hn.symm⟩
  exact Open.ChartEvaluation.Hodge.openPureFormsInDegree_mem_filtration U n i r hr a
    ((Open.ChartEvaluation.Hodge.mem_openPureFormsInDegree_iff U n i a).mpr ha)

theorem exists_local_filtered_reduction (U : Opens M) (n p k : ℕ) (hpk : p + k ≤ n + 1)
    (a : Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm E U (n + 1)) (ha : a ∈ Open.FiltrationDescent.Hodge.openFormFiltration U (n + 1) (p : ℤ))
    (hd : Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm.d a = 0) (x : U) :
    ∃ V : Opens M, x.val ∈ V ∧ ∃ hV : V ≤ U,
      ∃ t : Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm E V n, ∃ c : Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm E V (n + 1),
        t ∈ Open.FiltrationDescent.Hodge.openFormFiltration V n (p : ℤ) ∧ Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm.d c = 0 ∧
        c ∈ Open.FiltrationDescent.Hodge.openFormFiltration V (n + 1) ((p + k : ℕ) : ℤ) ∧
        c + Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm.d t = Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm.restrict hV a := by
  induction k with
  | zero =>
      refine ⟨U, x.property, le_refl U, 0, a, Submodule.zero_mem _, hd, ha, ?_⟩
      rw [map_zero, add_zero, Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm.restrict_refl]
  | succ k ih =>
      obtain ⟨V, hxV, hV, t, b, htf, hbd, hbf, hsum⟩ := ih (by omega)
      have hdegree : n = (p + k) + (n - (p + k)) := by omega
      obtain ⟨W, hxW, hW, u, c, hup, hcd, hcf, hstep⟩ :=
        exists_local_filtered_correction V n (p + k) (n - (p + k)) hdegree b hbf hbd ⟨x, hxV⟩
      let t' := Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm.restrict hW t + u
      have huf : u ∈ Open.FiltrationDescent.Hodge.openFormFiltration W n (p : ℤ) :=
        openPure_mem_filtration W n (p + k) (n - (p + k)) hdegree (p : ℤ) (by omega) u hup
      have ht'f : t' ∈ Open.FiltrationDescent.Hodge.openFormFiltration W n (p : ℤ) :=
        Submodule.add_mem _ (Open.FiltrationDescent.Hodge.openFormFiltration_restrict hW n _ t htf) huf
      have hsum' : c + Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm.d t' = Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm.restrict (hW.trans hV) a := by
        have hr := congrArg (Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm.restrict (n := n + 1) hW) hsum
        rw [map_add, Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm.restrict_d, Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm.restrict_trans] at hr
        calc
          c + Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm.d t' =
              (c + Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm.d u) +
                Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm.d (Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm.restrict hW t) := by
            change c + Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm.d (Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm.restrict hW t + u) = _
            rw [map_add]
            abel
          _ = _ := by rw [hstep]; exact hr
      refine ⟨W, hxW, hW.trans hV, t', c, ht'f, hcd, ?_, hsum'⟩
      simpa only [Nat.cast_add, Nat.cast_succ, add_assoc] using hcf

end

end OAI.AlgebraicGeometry.Comparison.Betti.FilteredLocalIteration.Hodge

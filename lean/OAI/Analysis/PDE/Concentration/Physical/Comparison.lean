import OAI.Analysis.PDE.Concentration.SpatialBarrier
import OAI.Analysis.PDE.Concentration.SpatialSplit

noncomputable section
namespace OAI.Analysis.PDE.Concentration

open Set Filter Module OAI.Analysis.Calculus.Current OAI.Analysis.Calculus.Quaternion OAI.Analysis.PDE.Dirichlet OAI.Analysis.PDE.Green OAI.LinearAlgebra.Moore
open scoped Topology ContDiff Matrix ComplexOrder

/-- Comparison on the actual physical spatial fiber, with arbitrary real
lattice. The compact transverse domain and the smooth defining extension are
constructed here from the rational physical defining function. -/
theorem physical_spatial_comparison (d : ℕ) (a : ℝ) (τ : ℂ)
    (ha : 0 < a) (ht : a ≤ ‖τ‖) (ht' : ‖τ‖ ≤ 4 * a)
    (b : Basis (Fin (d + 1)) ℝ (Fin (d + 1) → ℝ))
    {f g : OAI.Analysis.PDE.Dirichlet.CoordinateSpace (d + 1) 3 → ℝ}
    (hf : ContDiffOn ℝ 2 f {x | spatialDefiningFunction d a τ x < 0})
    (hg : ContDiffOn ℝ 2 g {x | spatialDefiningFunction d a τ x < 0})
    (hfc : ContinuousOn f {x | spatialDefiningFunction d a τ x ≤ 0})
    (hgc : ContinuousOn g {x | spatialDefiningFunction d a τ x ≤ 0})
    (hfper : OAI.Analysis.PDE.Dirichlet.LatticePeriodic (physicalSpatialSplit d) b f)
    (hgper : OAI.Analysis.PDE.Dirichlet.LatticePeriodic (physicalSpatialSplit d) b g)
    (hfpos : ∀ x, spatialDefiningFunction d a τ x < 0 →
      (OAI.LinearAlgebra.Moore.complexify (OAI.Analysis.PDE.Dirichlet.quaternionHessian OAI.Analysis.Calculus.Quaternion.threeSlots f x)).PosDef)
    (hdet : ∀ x, spatialDefiningFunction d a τ x < 0 →
      OAI.LinearAlgebra.Moore.mooreDet (d + 1) (OAI.Analysis.PDE.Dirichlet.quaternionHessian OAI.Analysis.Calculus.Quaternion.threeSlots g x) ≤
        OAI.LinearAlgebra.Moore.mooreDet (d + 1) (OAI.Analysis.PDE.Dirichlet.quaternionHessian OAI.Analysis.Calculus.Quaternion.threeSlots f x))
    (hbd : ∀ x, spatialDefiningFunction d a τ x = 0 → f x ≤ g x) :
    ∀ x, spatialDefiningFunction d a τ x ≤ 0 → f x ≤ g x := by
  obtain ⟨R, V, hR, _, heq, hneg, hle⟩ := OAI.Analysis.PDE.Green.exists_physical_global_extensions (d := d) a τ ha ht
  let r : OAI.Analysis.PDE.Dirichlet.CoordinateSpace (d + 1) 3 → ℝ := fun x => R (OAI.Analysis.PDE.Green.physicalSpatialProjection d x)
  have hr : ContDiff ℝ 2 r := (hR.of_le (by norm_num)).comp (OAI.Analysis.PDE.Green.physicalSpatialProjection d).contDiff
  have hD : {x | r x < 0} = {x | spatialDefiningFunction d a τ x < 0} := by
    ext x
    exact hneg _
  have hDc : {x | r x ≤ 0} = {x | spatialDefiningFunction d a τ x ≤ 0} := by
    ext x
    exact hle _
  have hreg (x : OAI.Analysis.PDE.Dirichlet.CoordinateSpace (d + 1) 3) (hx : r x ≤ 0) :
      OAI.Analysis.PDE.Green.physicalSpatialProjection d x ∈ OAI.Analysis.Calculus.Current.physicalRegularDomain τ :=
    OAI.Analysis.Calculus.Current.physical_fiber_collar_subset_regular a τ ha ht
      (((hle _).mp hx).trans (show (0 : ℝ) ≤ 1 by norm_num))
  have hgerm (x : OAI.Analysis.PDE.Dirichlet.CoordinateSpace (d + 1) 3) (hx : r x ≤ 0) :
      r =ᶠ[𝓝 x] spatialDefiningFunction d a τ :=
    ((heq _ ((hle _).mp hx)).1).comp_tendsto (OAI.Analysis.PDE.Green.physicalSpatialProjection d).continuous.continuousAt
  have hzero (x : OAI.Analysis.PDE.Dirichlet.CoordinateSpace (d + 1) 3) (hx : r x = 0) :
      spatialDefiningFunction d a τ x = 0 := by
    rw [← (hgerm x hx.le).self_of_nhds]
    exact hx
  have hresult := slots_dirichlet_comparison_lattice (by omega : 1 ≤ d + 1) OAI.Analysis.Calculus.Quaternion.threeSlots
    (physicalSpatialSplit d) b
    (OAI.Analysis.Calculus.Current.isCompact_physical_fiber_sublevel (d := d) a τ ha ht (0 : ℝ) (by norm_num))
    (hD.symm ▸ hf) (hD.symm ▸ hg) hr (hDc.symm ▸ hfc) (hDc.symm ▸ hgc)
    (fun x hx => by simpa only [physicalSpatialSplit_snd, Set.mem_ofPred_eq] using (hle _).mp hx)
    (transverse_latticePeriodic b R) hfper hgper
    (fun x hx => by
      rw [OAI.Analysis.PDE.Dirichlet.quaternionHessian_congr_germ OAI.Analysis.Calculus.Quaternion.threeSlots (hgerm x hx.le),
        quaternionHessian_spatialDefiningFunction d a τ x (hreg x hx.le)]
      exact spatial_defining_matrix_posDef d a τ _ ha ht ht' ((hle _).mp hx.le))
    (fun x hx => hfpos x ((hneg _).mp hx))
    (fun x hx => hdet x ((hneg _).mp hx))
    (fun x hx => hbd x (hzero x hx))
  intro x hx
  exact hresult x ((hle _).mpr hx)

/-- The actual Dirichlet solution is bounded below by a multiple of the
physical defining function whenever its prescribed determinant density is
dominated by the explicit barrier determinant. No solution bound or
comparison principle is assumed. -/
theorem physical_input_solution_bound (n : ℕ) :
    ∃ c : ℝ, 0 < c ∧ ∀ (a : ℝ) (τ : ℂ),
      0 < a → a ≤ ‖τ‖ → ‖τ‖ ≤ 4 * a →
      ∀ (basis : Basis (Fin (n + 2)) ℝ (Fin (n + 2) → ℝ))
        (u μ : OAI.Analysis.PDE.Dirichlet.CoordinateSpace (n + 2) 3 → ℝ) (b lam : ℝ),
      0 < b → 0 ≤ lam →
      ContDiffOn ℝ 2 u {x | spatialDefiningFunction (n + 1) a τ x < 0} →
      ContinuousOn u {x | spatialDefiningFunction (n + 1) a τ x ≤ 0} →
      OAI.Analysis.PDE.Dirichlet.LatticePeriodic (physicalSpatialSplit (n + 1)) basis u →
      (∀ x, spatialDefiningFunction (n + 1) a τ x = 0 → u x = 0) →
      (∀ x, spatialDefiningFunction (n + 1) a τ x < 0 →
        OAI.LinearAlgebra.Moore.mooreDet (n + 2) (OAI.Analysis.PDE.Dirichlet.quaternionHessian OAI.Analysis.Calculus.Quaternion.threeSlots
          (fun y => lam * spatialBackgroundFunction (n + 1) τ y + u y) x) = lam * μ x) →
      (∀ x, spatialDefiningFunction (n + 1) a τ x < 0 → μ x ≤ (b * (c / a ^ 2)) ^ (n + 1)) →
      ∀ x, spatialDefiningFunction (n + 1) a τ x ≤ 0 →
        b * spatialDefiningFunction (n + 1) a τ x ≤ u x ∧ -u x ≤ b := by
  obtain ⟨c, hc, hbar⟩ := spatial_input_barrier_determinant n
  refine ⟨c, hc, ?_⟩
  intro a τ ha ht ht' basis u μ b lam hb hlam hu huc huper hubd hPDE hμ
  have hc2 (x : OAI.Analysis.PDE.Dirichlet.CoordinateSpace (n + 2) 3)
      (hx : spatialDefiningFunction (n + 1) a τ x ≤ 0) :=
    spatial_functions_contDiffAt (n + 1) a τ x
      (OAI.Analysis.Calculus.Current.physical_fiber_collar_subset_regular a τ ha ht
        (hx.trans (show (0 : ℝ) ≤ 1 by norm_num)))
  have hr2 : ContDiffOn ℝ 2 (spatialDefiningFunction (n + 1) a τ)
      {x | spatialDefiningFunction (n + 1) a τ x < 0} :=
    fun x hx => (hc2 x hx.le).1.contDiffWithinAt
  have hB2 : ContDiffOn ℝ 2 (spatialBackgroundFunction (n + 1) τ)
      {x | spatialDefiningFunction (n + 1) a τ x < 0} :=
    fun x hx => (hc2 x hx.le).2.contDiffWithinAt
  have hrc : ContinuousOn (spatialDefiningFunction (n + 1) a τ)
      {x | spatialDefiningFunction (n + 1) a τ x ≤ 0} :=
    fun x hx => (hc2 x hx).1.continuousAt.continuousWithinAt
  have hBc : ContinuousOn (spatialBackgroundFunction (n + 1) τ)
      {x | spatialDefiningFunction (n + 1) a τ x ≤ 0} :=
    fun x hx => (hc2 x hx).2.continuousAt.continuousWithinAt
  have hBp : OAI.Analysis.PDE.Dirichlet.LatticePeriodic (physicalSpatialSplit (n + 1)) basis
      (spatialBackgroundFunction (n + 1) τ) :=
    transverse_latticePeriodic basis (fun q => ‖OAI.Analysis.Calculus.Current.phi (OAI.Analysis.Calculus.Current.physicalEmbedding τ q)‖ ^ 2)
  have hrp : OAI.Analysis.PDE.Dirichlet.LatticePeriodic (physicalSpatialSplit (n + 1)) basis
      (spatialDefiningFunction (n + 1) a τ) :=
    transverse_latticePeriodic basis (OAI.Analysis.Calculus.Current.physicalFiberDefining (1 / 10) a τ)
  have hcmp := physical_spatial_comparison (n + 1) a τ ha ht ht' basis
    (f := fun y => lam * spatialBackgroundFunction (n + 1) τ y + b * spatialDefiningFunction (n + 1) a τ y)
    (g := fun y => lam * spatialBackgroundFunction (n + 1) τ y + u y)
    ((contDiffOn_const.mul hB2).add (contDiffOn_const.mul hr2))
    ((contDiffOn_const.mul hB2).add hu)
    ((hBc.const_mul lam).add (hrc.const_mul b)) ((hBc.const_mul lam).add huc)
    (fun x l => by simp only [hBp x l, hrp x l])
    (fun x l => by simp only [hBp x l, huper x l])
    (fun x hx => spatial_input_barrier_posDef (n + 1) a τ x ha ht ht' hx.le hb hlam)
    (fun x hx => by
      rw [hPDE x hx]
      exact (mul_le_mul_of_nonneg_left (hμ x hx) hlam).trans
        (hbar a τ x ha ht ht' hx.le b lam hb hlam))
    (fun x hx => by rw [hx, hubd x hx]; simp)
  intro x hx
  have hbnd : b * spatialDefiningFunction (n + 1) a τ x ≤ u x := by
    have := hcmp x hx
    linarith
  refine ⟨hbnd, ?_⟩
  have hrbound := OAI.Analysis.Calculus.Current.physicalFiberDefining_ge_neg_one (1 / 10) a τ
    (OAI.Analysis.PDE.Green.physicalSpatialProjection (n + 1) x)
  change -1 ≤ spatialDefiningFunction (n + 1) a τ x at hrbound
  nlinarith

end OAI.Analysis.PDE.Concentration

import OAI.Analysis.PDE.Dirichlet.Boundary.Pointwise
import OAI.Analysis.PDE.Dirichlet.InteriorPointwise
import OAI.Analysis.PDE.Dirichlet.PointwiseSchauderAbsorption

open Set Metric Module InnerProductSpace
noncomputable section
namespace OAI.Analysis.PDE.Dirichlet

open OAI.Analysis.PDE.Elliptic OAI.Analysis.PDE.Schauder OAI.Analysis.Normed.Function.Holder

variable {m : ℕ} {P V ι I : Type*}
  [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup V] [NormedSpace ℝ V] [Fintype ι]
local notation "E" => EuclideanSpace ℝ (Fin m)
local instance periodicFamilyFirstGroup : NormedAddCommGroup (E →L[ℝ] ℝ) := inferInstance
local instance periodicFamilyFirstSpace : NormedSpace ℝ (E →L[ℝ] ℝ) := inferInstance
local instance periodicFamilySecondGroup : NormedAddCommGroup (E →L[ℝ] E →L[ℝ] ℝ) := inferInstance
local instance periodicFamilySecondSpace : NormedSpace ℝ (E →L[ℝ] E →L[ℝ] ℝ) := inferInstance

/-- Uniform global periodic Schauder estimate for an arbitrary family of
actual equations. Local chart constants need not be uniform: their radii
precede the small error and compactness selects finitely many charts. -/
theorem periodic_schauder_family (hm : 3 ≤ m)
    (e : E ≃L[ℝ] P × V) (b : Basis ι ℝ P) {K : Set V} (hK : IsCompact K)
    (r : E → ℝ) (hr : ContDiff ℝ 3 r) (hrp : LatticePeriodic e b r)
    (hbounded : ∀ x, r x ≤ 0 → (e x).2 ∈ K)
    (hreg : ∀ x, r x = 0 → fderiv ℝ r x ≠ 0)
    {hΩD : {x | r x < 0} ⊆ {x | r x ≤ 0}}
    {α ell Λ N : ℝ} (hα : 0 < α) (hα1 : α < 1)
    (hell : 0 < ell) (hΛ : 0 ≤ Λ) (hN : 0 ≤ N)
    (A : I → E → E →L[ℝ] E) (hA : ∀ i, Continuous (A i))
    (hAs : ∀ i x, r x ≤ 0 → (A i x).toLinearMap.IsSymmetric)
    (hAl : ∀ i x, r x ≤ 0 → ∀ z, ell*‖z‖^2 ≤ inner ℝ z (A i x z))
    (hAu : ∀ i x, r x ≤ 0 → ∀ z, inner ℝ z (A i x z) ≤ Λ*‖z‖^2)
    (hAn : ∀ i x, r x ≤ 0 → ‖A i x‖ ≤ N)
    (hAh : ∀ i x, r x ≤ 0 → ∀ y, r y ≤ 0 →
      ‖A i x-A i y‖ ≤ N*dist x y^α)
    (u : I → E → ℝ) (hu : ∀ i, ContDiff ℝ 3 (u i))
    (hup : ∀ i, LatticePeriodic e b (u i))
    (hu0 : ∀ i x, r x = 0 → u i x = 0)
    (F : I → E → ℝ) (B M : I → ℝ) (hB : ∀ i, 0 ≤ B i) (hM : ∀ i, 0 ≤ M i)
    (hFn : ∀ i x, r x ≤ 0 → |F i x| ≤ B i)
    (hFh : ∀ i x, r x ≤ 0 → ∀ y, r y ≤ 0 →
      |F i x-F i y| ≤ B i*dist x y^α)
    (hun : ∀ i x, r x ≤ 0 → |u i x| ≤ M i)
    (heq : ∀ i x, r x ≤ 0 → OAI.Analysis.PDE.Elliptic.ellipticTrace (A i) (u i) x = F i x)
    (U : I → OAI.Analysis.Normed.Function.Holder.C2Holder (F := ℝ) hΩD α)
    (hU0 : ∀ i x, OAI.Analysis.Normed.Function.Holder.C2Holder.value (U i) x = u i x)
    (hU1 : ∀ i x, OAI.Analysis.Normed.Function.Holder.C2Holder.firstDerivative (U i) x = fderiv ℝ (u i) x)
    (hU2 : ∀ i x, OAI.Analysis.Normed.Function.Holder.C2Holder.secondDerivative (U i) x = fderiv ℝ (fderiv ℝ (u i)) x) :
    ∃ C > 0, ∀ i, ‖U i‖ ≤ C*(B i+M i) := by
  apply lattice_C2Holder_norm_absorption_of_pointwise e b hK hr.continuous hrp hbounded hα
    u hup U hU0 hU1 hU2 (fun i => B i+M i) (fun i => add_nonneg (hB i) (hM i))
  intro x
  have hx : r (x : E) ≤ 0 := x.property.2
  rcases lt_or_eq_of_le hx with hxi | hxb
  · have hopen : IsOpen {z : E | r z < 0} := isOpen_lt hr.continuous continuous_const
    obtain ⟨ρ, hρ, hρball⟩ := Metric.isOpen_iff.mp hopen x hxi
    have hρclosed : closedBall (x : E) (ρ/2) ⊆ {z : E | r z ≤ 0} := by
      intro z hz
      have hzb : z ∈ ball (x : E) ρ := lt_of_le_of_lt hz (half_lt_self hρ)
      have hzneg : r z < 0 := hρball hzb
      exact hzneg.le
    obtain ⟨δ, hδ, hlocal⟩ := interior_pointwise_schauder (hΩK := hΩD)
      hm hα hα1 hell hΛ hN (half_pos hρ) x hρclosed
    refine ⟨δ, hδ, ?_⟩
    intro ε hε
    obtain ⟨D, hD, hestimate⟩ := hlocal ε hε
    refine ⟨D, hD, ?_⟩
    intro i y hy
    obtain ⟨hjets, hholder⟩ := hestimate (A i) (hAs i) (hAn i)
      (by simpa only [Set.mem_ofPred_eq, dist_eq_norm] using hAh i) (hAl i x hx) (hAu i x hx)
      (u i) (hu i) (F i) (U i) (hU0 i) (hU1 i) (hU2 i) (B i) (M i) (hB i) (hM i)
      (by simpa only [Set.mem_ofPred_eq, Real.norm_eq_abs] using hun i)
      (by simpa only [Set.mem_ofPred_eq, Real.norm_eq_abs] using hFn i)
      (by simpa only [Set.mem_ofPred_eq, Real.norm_eq_abs, dist_eq_norm] using hFh i) (heq i)
    have hyball : (y : E) ∈ closedBall (x : E) δ := hy
    obtain ⟨h0, h1, h2⟩ := hjets y hyball
    refine ⟨h0, h1, h2, ?_⟩
    intro z hz
    have hzball : (z : E) ∈ closedBall (x : E) δ := hz
    simpa only [Subtype.dist_eq, dist_eq_norm] using hholder y hyball z hzball
  · let k : Fin m := ⟨0, by omega⟩
    obtain ⟨δ, hδ, hlocal⟩ := boundary_pointwise_schauder (hΩD := hΩD)
      hm k r hr x hxb (hreg x hxb) hell hΛ hN hα hα1
    refine ⟨δ, hδ, ?_⟩
    intro ε hε
    obtain ⟨D, hD, hestimate⟩ := hlocal ε hε
    refine ⟨D, hD, ?_⟩
    intro i y hy
    have hjet := hestimate (A i) (hA i) (hAs i) (hAl i) (hAu i) (hAn i) (hAh i)
      (u i) (hu i) (hu0 i) (F i) (B i) (M i) (hB i) (hM i)
      (hFn i) (hFh i) (hun i) (heq i) (U i) (hU0 i) (hU1 i) (hU2 i)
    have hyball : (y : E) ∈ closedBall (x : E) δ ∩ {z | r z ≤ 0} := ⟨hy, y.property.2⟩
    refine ⟨?_, hjet.first y hyball, hjet.second y hyball, ?_⟩
    · simpa only [Real.norm_eq_abs] using hjet.value y hyball
    intro z hz
    have hzball : (z : E) ∈ closedBall (x : E) δ ∩ {z | r z ≤ 0} := ⟨hz, z.property.2⟩
    simpa only [Subtype.dist_eq, dist_eq_norm] using hjet.second_holder y hyball z hzball

end OAI.Analysis.PDE.Dirichlet

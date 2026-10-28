import OAI.Analysis.PDE.Schauder.Calculus.Schauder.BanachData

/-! The genuine Newtonian and Poisson inverses as bounded linear maps of Hölder spaces. -/

noncomputable section
open _root_.MeasureTheory Set Metric Laplacian
open scoped BoundedContinuousFunction
namespace OAI.Analysis.PDE.Schauder

open OAI.Analysis.Normed.Function.Holder

local instance inverseFirstNormedGroup (m : ℕ) :
    NormedAddCommGroup (EuclideanSpace ℝ (Fin m) →L[ℝ] ℝ) := inferInstance
local instance inverseFirstNormedSpace (m : ℕ) :
    NormedSpace ℝ (EuclideanSpace ℝ (Fin m) →L[ℝ] ℝ) := inferInstance
local instance inverseSecondNormedGroup (m : ℕ) :
    NormedAddCommGroup (EuclideanSpace ℝ (Fin m) →L[ℝ] EuclideanSpace ℝ (Fin m) →L[ℝ] ℝ) := inferInstance
local instance inverseSecondNormedSpace (m : ℕ) :
    NormedSpace ℝ (EuclideanSpace ℝ (Fin m) →L[ℝ] EuclideanSpace ℝ (Fin m) →L[ℝ] ℝ) := inferInstance
local instance inverseGlobalNormedGroup (m : ℕ) (α : ℝ) :
    NormedAddCommGroup (GlobalC2Holder m α) := inferInstance
local instance inverseGlobalNormedSpace (m : ℕ) (α : ℝ) :
    NormedSpace ℝ (GlobalC2Holder m α) := inferInstance

theorem newtonianPotential_add {m : ℕ} (hm : 1 ≤ m)
    (f g : EuclideanSpace ℝ (Fin m) → ℝ) (hf : Continuous f) (hg : Continuous g)
    (hfc : HasCompactSupport f) (hgc : HasCompactSupport g) :
    newtonianPotential (f + g) = newtonianPotential f + newtonianPotential g := by
  funext x
  simp only [newtonianPotential, Pi.add_apply, mul_add]
  exact integral_add (newtonianPotential_integrable hm f hf hfc x)
    (newtonianPotential_integrable hm g hg hgc x)

theorem newtonianPotential_smul {m : ℕ}
    (c : ℝ) (f : EuclideanSpace ℝ (Fin m) → ℝ) :
    newtonianPotential (c • f) = c • newtonianPotential f := by
  funext x
  simp only [newtonianPotential, Pi.smul_apply, smul_eq_mul, mul_left_comm _ c]
  exact integral_const_mul c _

theorem exists_newtonianHolder_operator {m : ℕ} (hm : 2 ≤ m)
    {α : ℝ} (hα : 0 < α) (hα1 : α < 1) (R : ℝ) :
    ∃ T : SupportedHolder m α R →L[ℝ] GlobalC2Holder m α,
      ∀ f x, OAI.Analysis.Normed.Function.Holder.C2Holder.value (T f) ⟨x, mem_univ x⟩ = newtonianPotential (OAI.Analysis.PDE.Schauder.SupportedHolder.value f) x := by
  obtain ⟨C, hC, hc⟩ := newtonianPotential_holder_bounds hm hα hα1 (R + 1)
  have hlift (f : SupportedHolder m α R) :
      ∃ u : GlobalC2Holder m α,
        (∀ x, OAI.Analysis.Normed.Function.Holder.C2Holder.value u ⟨x, mem_univ x⟩ = newtonianPotential (OAI.Analysis.PDE.Schauder.SupportedHolder.value f) x) ∧
        ‖u‖ ≤ C * ‖f‖ := by
    have hb := hc (OAI.Analysis.PDE.Schauder.SupportedHolder.value f) f.continuous f.hasCompactSupport
      f.support_subset_ball ‖f‖ (norm_nonneg f) f.norm_value_le f.holder
    have hreg := (newtonianPotential_C2_limit hm (OAI.Analysis.PDE.Schauder.SupportedHolder.value f) f.continuous
      f.hasCompactSupport (norm_nonneg f) hα hα1 f.holder).1
    let u : GlobalC2Holder m α := OAI.Analysis.Normed.Function.Holder.C2Holder.ofContDiff isOpen_univ Subset.rfl hα.le
      (newtonianPotential (OAI.Analysis.PDE.Schauder.SupportedHolder.value f)) hreg
      (fun x _ => hb.1 x) (fun x _ => hb.2.1 x) (fun x _ => hb.2.2.1 x)
      (fun x _ y _ => by simpa only [dist_eq_norm] using hb.2.2.2 x y)
    refine ⟨u, fun x => rfl, ?_⟩
    apply OAI.Analysis.Normed.Function.Holder.C2Holder.norm_le_of_bounds hα.le (mul_nonneg hC.le (norm_nonneg f))
    · intro x
      exact hb.1 x
    · intro x
      exact hb.2.1 x
    · intro x
      exact hb.2.2.1 x
    · intro x y
      change ‖fderiv ℝ (fderiv ℝ (newtonianPotential (OAI.Analysis.PDE.Schauder.SupportedHolder.value f))) x -
        fderiv ℝ (fderiv ℝ (newtonianPotential (OAI.Analysis.PDE.Schauder.SupportedHolder.value f))) y‖ ≤
          C * ‖f‖ * (dist x y) ^ α
      simpa only [Subtype.dist_eq, dist_eq_norm] using! hb.2.2.2 x y
  choose u hu hn using hlift
  have hinj : Function.Injective (OAI.Analysis.Normed.Function.Holder.C2Holder.value (F := ℝ)
      (hΩK := (show (univ : Set (EuclideanSpace ℝ (Fin m))) ⊆ univ from Subset.rfl)) (α := α)) :=
    OAI.Analysis.Normed.Function.Holder.C2Holder.value_injective (by simp)
  let T : SupportedHolder m α R →ₗ[ℝ] GlobalC2Holder m α := {
    toFun := u
    map_add' := by
      intro f g
      apply hinj
      apply BoundedContinuousFunction.ext
      intro x
      change OAI.Analysis.Normed.Function.Holder.C2Holder.value (u (f + g)) x = OAI.Analysis.Normed.Function.Holder.C2Holder.value (u f) x + OAI.Analysis.Normed.Function.Holder.C2Holder.value (u g) x
      rw [hu, hu, hu, OAI.Analysis.PDE.Schauder.SupportedHolder.value_add,
        newtonianPotential_add (show 1 ≤ m by omega) _ _ f.continuous g.continuous f.hasCompactSupport g.hasCompactSupport]
      rfl
    map_smul' := by
      intro c f
      apply hinj
      apply BoundedContinuousFunction.ext
      intro x
      change OAI.Analysis.Normed.Function.Holder.C2Holder.value (u (c • f)) x = c * OAI.Analysis.Normed.Function.Holder.C2Holder.value (u f) x
      rw [hu, hu, OAI.Analysis.PDE.Schauder.SupportedHolder.value_smul, newtonianPotential_smul]
      rfl }
  refine ⟨T.mkContinuous C (fun f => hn f), ?_⟩
  intro f x
  exact hu f x

def newtonianHolderOperator {m : ℕ} (hm : 2 ≤ m)
    {α : ℝ} (hα : 0 < α) (hα1 : α < 1) (R : ℝ) :
    SupportedHolder m α R →L[ℝ] GlobalC2Holder m α :=
  (exists_newtonianHolder_operator hm hα hα1 R).choose

theorem newtonianHolderOperator_value {m : ℕ} (hm : 2 ≤ m)
    {α : ℝ} (hα : 0 < α) (hα1 : α < 1) (R : ℝ)
    (f : SupportedHolder m α R) (x : EuclideanSpace ℝ (Fin m)) :
    OAI.Analysis.Normed.Function.Holder.C2Holder.value (newtonianHolderOperator hm hα hα1 R f) ⟨x, mem_univ x⟩ =
      newtonianPotential (OAI.Analysis.PDE.Schauder.SupportedHolder.value f) x :=
  (exists_newtonianHolder_operator hm hα hα1 R).choose_spec f x

def poissonHolderOperator {m : ℕ} (hm : 3 ≤ m)
    {α : ℝ} (hα : 0 < α) (hα1 : α < 1) (R : ℝ) :
    SupportedHolder m α R →L[ℝ] GlobalC2Holder m α :=
  (newtonianHolderOperator (m := m) (by omega) hα hα1 R).comp
    ((poissonNormalization m)⁻¹ • ContinuousLinearMap.id ℝ (SupportedHolder m α R))

theorem poissonHolderOperator_value {m : ℕ} (hm : 3 ≤ m)
    {α : ℝ} (hα : 0 < α) (hα1 : α < 1) (R : ℝ)
    (f : SupportedHolder m α R) (x : EuclideanSpace ℝ (Fin m)) :
    OAI.Analysis.Normed.Function.Holder.C2Holder.value (poissonHolderOperator hm hα hα1 R f) ⟨x, mem_univ x⟩ =
      poissonPotential (OAI.Analysis.PDE.Schauder.SupportedHolder.value f) x := by
  change OAI.Analysis.Normed.Function.Holder.C2Holder.value (newtonianHolderOperator (m := m) (by omega) hα hα1 R
    ((poissonNormalization m)⁻¹ • f)) ⟨x, mem_univ x⟩ = _
  rw [newtonianHolderOperator_value, OAI.Analysis.PDE.Schauder.SupportedHolder.value_smul, newtonianPotential_smul]
  rfl

theorem poissonHolderOperator_solves {m : ℕ} (hm : 3 ≤ m)
    {α : ℝ} (hα : 0 < α) (hα1 : α < 1) (R : ℝ)
    (f : SupportedHolder m α R) (x : EuclideanSpace ℝ (Fin m)) :
    laplacian (fun y => OAI.Analysis.Normed.Function.Holder.C2Holder.value (poissonHolderOperator hm hα hα1 R f) ⟨y, mem_univ y⟩) x =
      OAI.Analysis.PDE.Schauder.SupportedHolder.value f x := by
  simp only [poissonHolderOperator_value]
  exact laplacian_poissonPotential_holder hm _ f.continuous f.hasCompactSupport
    (norm_nonneg f) hα hα1 f.holder x

end OAI.Analysis.PDE.Schauder

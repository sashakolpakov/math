import OAI.Geometry.ComplexTorus.RiemannProjectivity.HolomorphicRegularityAt
import Mathlib.Topology.Covering.Basic
import Mathlib.Topology.Maps.Proper.Basic
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ContDiff

/-! # Finite Branches At -/

namespace OAI.Geometry.ComplexTorus.RiemannProjectivity.FiniteBranchesAt.Constructions.FiniteBranches

noncomputable section

/-!
# RiemannProjectivity: finite branches over regular values of a proper map

Properness makes every regular fiber compact and discrete, hence finite.
The regular values form an open set and are evenly covered. A holomorphic
map with invertible derivative supplies the local inverses used here.
-/

open Set Filter
open scoped _root_.Topology ContDiff

section Topology

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]

def LocalInverseAt (f : X → Y) (x : X) : Prop :=
  ∃ e : OpenPartialHomeomorph X Y, x ∈ e.source ∧ (e : X → Y) = f

def regularValues (f : X → Y) : Set Y :=
  {y | ∀ x, f x = y → LocalInverseAt f x}

theorem isOpen_localInverseLocus (f : X → Y) : IsOpen {x | LocalInverseAt f x} := by
  apply isOpen_iff_mem_nhds.mpr
  rintro x ⟨e, hx, he⟩
  exact mem_of_superset (e.open_source.mem_nhds hx) (fun z hz => ⟨e, hz, he⟩)

theorem isOpen_regularValues {f : X → Y} (hf : IsClosedMap f) :
    IsOpen (regularValues f) := by
  have heq : regularValues f = (f '' {x | ¬LocalInverseAt f x})ᶜ := by
    ext y
    simp only [regularValues, mem_ofPred_eq, mem_compl_iff, mem_image,
      not_exists, not_and]
    constructor
    · exact fun h x hx hxy => hx (h x hxy)
    · intro h x hxy
      by_contra hx
      exact h x hx hxy
  rw [heq]
  exact (hf _ (isOpen_localInverseLocus f).isClosed_compl).isOpen_compl

theorem finite_regular_fiber [T2Space X] {f : X → Y} (hf : IsProperMap f)
    {y : Y} (hy : y ∈ regularValues f) : (f ⁻¹' {y}).Finite := by
  apply (hf.isCompact_preimage isCompact_singleton).finite
  exact IsDiscrete.of_openPartialHomeomorph f subset_rfl (fun x hx => hy x hx)

theorem evenlyCovered_regular_value [T2Space X] {f : X → Y} (hf : IsProperMap f)
    {y : Y} (hy : y ∈ regularValues f) : IsEvenlyCovered f y (f ⁻¹' {y}) :=
  hf.isClosedMap.isEvenlyCovered_of_openPartialHomeomorph
    (finite_regular_fiber hf hy) (fun x hx => hy x hx)

theorem covering_regularValues [T2Space X] {f : X → Y} (hf : IsProperMap f) :
    IsCoveringMapOn f (regularValues f) := fun _ hy => evenlyCovered_regular_value hf hy

end Topology

variable {V W : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]
  [NormedAddCommGroup W] [NormedSpace ℂ W]
  [FiniteDimensional ℂ V] [FiniteDimensional ℂ W]

/-- The local inverse of a holomorphic map is holomorphic wherever its
derivative is invertible. Both directions are actual functions on open sets. -/
theorem holomorphic_local_inverse {f : V → W} {U : Set V} (hU : IsOpen U)
    (hf : DifferentiableOn ℂ f U) {x : V} (hx : x ∈ U)
    (hd : Function.Bijective (fderiv ℂ f x)) :
    ∃ e : OpenPartialHomeomorph V W, x ∈ e.source ∧ (e : V → W) = f ∧
      DifferentiableOn ℂ e.symm e.target := by
  let : CompleteSpace V := FiniteDimensional.complete ℂ V
  let : CompleteSpace W := FiniteDimensional.complete ℂ W
  have hc := HolomorphicRegularityAt.Constructions.HolomorphicRegularity.contDiffAt_one_of_differentiableOn hU hf hx
  let L : V ≃L[ℂ] W := ContinuousLinearEquiv.ofBijective (fderiv ℂ f x)
    (LinearMap.ker_eq_bot.mpr hd.1) (LinearMap.range_eq_top.mpr hd.2)
  have hdL : HasFDerivAt f (L : V →L[ℂ] W) x :=
    ((hf x hx).differentiableAt (hU.mem_nhds hx)).hasFDerivAt
  let e₀ := hc.toOpenPartialHomeomorph f hdL (by norm_num)
  let e := e₀.restrContDiff ℂ 1 (by norm_num)
  refine ⟨e, ?_, ?_, ?_⟩
  · exact ⟨hc.mem_toOpenPartialHomeomorph_source hdL (by norm_num),
      hc, hc.to_localInverse hdL (by norm_num)⟩
  · exact hc.toOpenPartialHomeomorph_coe hdL (by norm_num)
  · exact (e₀.contDiffOn_restrContDiff_target ℂ (by norm_num : (1 : ℕ∞ω) ≠ ∞)).differentiableOn
      (by norm_num)

theorem localInverseAt_of_bijective_fderiv {f : V → W} {U : Set V} (hU : IsOpen U)
    (hf : DifferentiableOn ℂ f U) {x : V} (hx : x ∈ U)
    (hd : Function.Bijective (fderiv ℂ f x)) : LocalInverseAt f x := by
  obtain ⟨e, he, hef, _⟩ := holomorphic_local_inverse hU hf hx hd
  exact ⟨e, he, hef⟩

/-- At a regular value of a proper holomorphic map, all inverse branches
form a finite covering of a neighborhood. -/
theorem finite_covering_at_regular_value {f : V → W} (hf : IsProperMap f)
    (hd : Differentiable ℂ f) (y : W)
    (hreg : ∀ x, f x = y → Function.Bijective (fderiv ℂ f x)) :
    (f ⁻¹' {y}).Finite ∧ IsEvenlyCovered f y (f ⁻¹' {y}) := by
  have hy : y ∈ regularValues f := fun x hxy =>
    localInverseAt_of_bijective_fderiv isOpen_univ hd.differentiableOn (mem_univ x) (hreg x hxy)
  exact ⟨finite_regular_fiber hf hy, evenlyCovered_regular_value hf hy⟩

end

end OAI.Geometry.ComplexTorus.RiemannProjectivity.FiniteBranchesAt.Constructions.FiniteBranches

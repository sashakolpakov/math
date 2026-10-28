import OAI.AlgebraicGeometry.ComplexGroups.HolomorphicAlgebraicity.MaximalRank
import Mathlib.Topology.MetricSpace.HausdorffDimension
import Mathlib.LinearAlgebra.Dimension.Free
import Mathlib.LinearAlgebra.Complex.FiniteDimensional
import Mathlib.Topology.Compactness.Lindelof

/-! # Holomorphic Dimension -/

namespace OAI.AlgebraicGeometry.ComplexGroups.HolomorphicAlgebraicity.HolomorphicDimension.Constructions.Dimension

noncomputable section

/-!
# Dimension bounds for holomorphic images

Holomorphic maps are locally Lipschitz in finite dimensions, so their images
cannot have larger Hausdorff dimension than their domains.
-/

open Set Filter
open scoped _root_.Topology

theorem dimH_holomorphic_image_le
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E]
    [NormedAddCommGroup F] [NormedSpace ℂ F] [FiniteDimensional ℂ F]
    {f : E → F} {U : Set E} (hU : IsOpen U) (hf : DifferentiableOn ℂ f U) :
    dimH (f '' U) ≤ (2 * Module.finrank ℂ E : ℕ) := by
  let : NormedSpace ℝ E := NormedSpace.restrictScalars ℝ ℂ E
  let : FiniteDimensional ℝ E := FiniteDimensional.trans ℝ ℂ E
  let : ProperSpace E := FiniteDimensional.proper ℝ E
  have hcd := HolomorphicRegularity.Constructions.Regularity.contDiffOn_one_of_differentiableOn_finiteDimensional hU hf
  have hdim : dimH (f '' U) ≤ dimH U := by
    apply dimH_image_le_of_locally_lipschitzOn
    intro x hx
    obtain ⟨C, V, hV, hLip⟩ := (hcd.contDiffAt (hU.mem_nhds hx)).exists_lipschitzOnWith
    exact ⟨C, V, nhdsWithin_le_nhds hV, hLip⟩
  apply hdim.trans
  apply (dimH_mono (subset_univ U)).trans_eq
  rw [Real.dimH_univ_eq_finrank, ← Module.finrank_mul_finrank ℝ ℂ E, Complex.finrank_real_complex]

theorem finrank_le_of_holomorphic_image_contains_open
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E]
    [NormedAddCommGroup F] [NormedSpace ℂ F] [FiniteDimensional ℂ F]
    {f : E → F} {U : Set E} (hU : IsOpen U) (hf : DifferentiableOn ℂ f U)
    {V : Set F} (hV : IsOpen V) (hne : V.Nonempty) (hVU : V ⊆ f '' U) :
    Module.finrank ℂ F ≤ Module.finrank ℂ E := by
  let : NormedSpace ℝ F := NormedSpace.restrictScalars ℝ ℂ F
  let : FiniteDimensional ℝ F := FiniteDimensional.trans ℝ ℂ F
  obtain ⟨y, hy⟩ := hne
  have hdim := (dimH_mono hVU).trans (dimH_holomorphic_image_le hU hf)
  rw [Real.dimH_of_mem_nhds (hV.mem_nhds hy), ← Module.finrank_mul_finrank ℝ ℂ F,
    Complex.finrank_real_complex] at hdim
  have hnat : 2 * Module.finrank ℂ F ≤ 2 * Module.finrank ℂ E := by exact_mod_cast hdim
  omega

theorem dimH_le_of_local_holomorphic_images
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E]
    [NormedAddCommGroup F] [NormedSpace ℂ F] [FiniteDimensional ℂ F]
    {S : Set F}
    (hparam : ∀ p ∈ S, ∃ (U : Set F) (V : Set E) (φ : E → F),
      IsOpen U ∧ p ∈ U ∧ IsOpen V ∧ DifferentiableOn ℂ φ V ∧ S ∩ U ⊆ φ '' V) :
    dimH S ≤ (2 * Module.finrank ℂ E : ℕ) := by
  classical
  let : ProperSpace F := FiniteDimensional.proper ℂ F
  choose U V φ hU hpU hV hφ hsub using (fun p : S => hparam p p.property)
  have hcover : S ⊆ ⋃ p : S, U p := fun p hp => mem_iUnion.mpr ⟨⟨p, hp⟩, hpU ⟨p, hp⟩⟩
  obtain ⟨r, hr, hrcov⟩ := (HereditarilyLindelofSpace.isLindelof S).elim_countable_subcover U hU hcover
  let : Countable r := hr.to_subtype
  have himages : S ⊆ ⋃ a : r, φ a.val '' V a.val := by
    intro p hp
    obtain ⟨a, ha⟩ := mem_iUnion.mp (hrcov hp)
    obtain ⟨har, hpa⟩ := mem_iUnion.mp ha
    exact mem_iUnion.mpr ⟨⟨a, har⟩, hsub a ⟨hp, hpa⟩⟩
  apply (dimH_mono himages).trans
  rw [dimH_iUnion]
  exact iSup_le (fun a => dimH_holomorphic_image_le (hV a.val) (hφ a.val))

theorem dimH_le_of_punctured_local_holomorphic_images
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E]
    [NormedAddCommGroup F] [NormedSpace ℂ F] [FiniteDimensional ℂ F]
    {S : Set F}
    (hparam : ∀ p ∈ S, p ≠ 0 → ∃ (U : Set F) (V : Set E) (φ : E → F),
      IsOpen U ∧ p ∈ U ∧ IsOpen V ∧ DifferentiableOn ℂ φ V ∧ S ∩ U ⊆ φ '' V) :
    dimH S ≤ (2 * Module.finrank ℂ E : ℕ) := by
  have hsmall : dimH {p : F | p ∈ S ∧ p ≠ 0} ≤ (2 * Module.finrank ℂ E : ℕ) := by
    apply dimH_le_of_local_holomorphic_images
    intro p hp
    obtain ⟨U, V, φ, hU, hpU, hV, hφ, hsub⟩ := hparam p hp.1 hp.2
    exact ⟨U, V, φ, hU, hpU, hV, hφ, fun y hy => hsub ⟨hy.1.1, hy.2⟩⟩
  have hsub : S ⊆ {0} ∪ {p : F | p ∈ S ∧ p ≠ 0} := by
    intro p hp
    by_cases hp0 : p = 0
    · exact Or.inl hp0
    · exact Or.inr ⟨hp, hp0⟩
  apply (dimH_mono hsub).trans
  rw [dimH_union, dimH_singleton]
  exact max_le zero_le hsmall

theorem finrank_eq_of_finite_surjective_parametrized_set
    {E A F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E]
    [NormedAddCommGroup A] [NormedSpace ℂ A] [FiniteDimensional ℂ A]
    [NormedAddCommGroup F] [NormedSpace ℂ F] [FiniteDimensional ℂ F]
    {S : Set A} (L : A →L[ℂ] F) (hsurj : L '' S = univ)
    (hfinite : ∀ v : F, {p | p ∈ S ∧ L p = v}.Finite)
    (hne : ∃ p ∈ S, p ≠ 0)
    (hparam : ∀ p ∈ S, p ≠ 0 → ∃ (U : Set A) (V : Set E) (φ : E → A),
      IsOpen U ∧ p ∈ U ∧ IsOpen V ∧ DifferentiableOn ℂ φ V ∧
      S ∩ U ⊆ φ '' V ∧ MapsTo φ V S ∧ InjOn φ V) :
    Module.finrank ℂ E = Module.finrank ℂ F := by
  have hupper : Module.finrank ℂ F ≤ Module.finrank ℂ E := by
    let : NormedSpace ℝ F := NormedSpace.restrictScalars ℝ ℂ F
    let : FiniteDimensional ℝ F := FiniteDimensional.trans ℝ ℂ F
    have hSdim : dimH S ≤ (2 * Module.finrank ℂ E : ℕ) :=
      dimH_le_of_punctured_local_holomorphic_images (fun p hp hp0 => by
        obtain ⟨U, V, φ, hU, hpU, hV, hφ, hsub, _, _⟩ := hparam p hp hp0
        exact ⟨U, V, φ, hU, hpU, hV, hφ, hsub⟩)
    have hdim := (L.lipschitzWith.dimH_image_le S).trans hSdim
    rw [hsurj, Real.dimH_univ_eq_finrank, ← Module.finrank_mul_finrank ℝ ℂ F,
      Complex.finrank_real_complex] at hdim
    have hnat : 2 * Module.finrank ℂ F ≤ 2 * Module.finrank ℂ E := by exact_mod_cast hdim
    omega
  apply le_antisymm _ hupper
  obtain ⟨p, hp, hp0⟩ := hne
  obtain ⟨U, V, φ, _, hpU, hV, hφ, hsub, hmaps, hinj⟩ := hparam p hp hp0
  obtain ⟨x, hx, _⟩ := hsub ⟨hp, hpU⟩
  have hcomp : DifferentiableOn ℂ (fun y => L (φ y)) V := L.differentiable.comp_differentiableOn hφ
  have hfib (v : F) : {y | y ∈ V ∧ L (φ y) = v}.Finite :=
    Set.Finite.of_injOn (f := φ) (s := {y | y ∈ V ∧ L (φ y) = v})
      (t := {p | p ∈ S ∧ L p = v}) (fun y hy => ⟨hmaps hy.1, hy.2⟩)
      (hinj.mono (fun _ hy => hy.1)) (hfinite v)
  obtain ⟨y, _, hyD⟩ := MaximalRank.Constructions.FiniteRank.exists_injective_fderiv_of_finite_fibers hV ⟨x, hx⟩ hcomp hfib
  exact LinearMap.finrank_le_finrank_of_injective hyD

end

end OAI.AlgebraicGeometry.ComplexGroups.HolomorphicAlgebraicity.HolomorphicDimension.Constructions.Dimension

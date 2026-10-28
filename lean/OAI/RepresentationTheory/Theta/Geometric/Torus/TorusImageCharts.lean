import OAI.Geometry.ComplexTorus.RiemannProjectivity.HolomorphicRegularityAt
import OAI.RepresentationTheory.Theta.Geometric.Torus.Root
import OAI.AlgebraicGeometry.ComplexPoints.Analytic.ImmersionNormalForm

/-! # Torus Image Charts -/

namespace OAI.RepresentationTheory.Theta.Geometric.Torus.TorusImageCharts.CM.Algebraization.ImageCharts

noncomputable section

open Set Filter
open scoped _root_.Topology ContDiff

open OAI.AlgebraicGeometry.ComplexPoints.Analytic.ImmersionNormalForm OAI.AlgebraicGeometry.Foundations.Scheme.ProjectiveCoordinatesIn.Algebraic.ProjectiveCoordinates

variable {V W : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]
  [NormedAddCommGroup W] [NormedSpace ℂ W]
  [FiniteDimensional ℂ V] [FiniteDimensional ℂ W]

/-- Holomorphic normal coordinates with the actual local image as their zero slice. -/
def HasHolomorphicNormalChart (f : V → W) (x : V) : Prop :=
  ∃ (C : Submodule ℂ W) (q : OpenPartialHomeomorph (V × C) W),
    (x, 0) ∈ q.source ∧
    (∀ y, q (y, 0) = f y) ∧
    DifferentiableOn ℂ q.symm q.target ∧
    ∀ y ∈ q.target, (q.symm y).2 = 0 ↔
      ∃ z, (z, 0) ∈ q.source ∧ f z = y

theorem hasHolomorphicNormalChart_of_injective_fderiv
    (f : V → W) (x : V) {U : Set V} (hU : IsOpen U) (hx : x ∈ U)
    (hf : DifferentiableOn ℂ f U) (hi : Function.Injective (fderiv ℂ f x)) :
    HasHolomorphicNormalChart f x := by
  let : CompleteSpace W := FiniteDimensional.complete ℂ W
  have hf1 := Geometry.ComplexTorus.RiemannProjectivity.HolomorphicRegularityAt.Constructions.HolomorphicRegularity.contDiffAt_one_of_differentiableOn hU hf hx
  obtain ⟨C, e, he⟩ := AlgebraicGeometry.ComplexPoints.Analytic.LinearImmersionComplement.exists_linearImmersionComplement (fderiv ℂ f x) hi
  let : CompleteSpace (V × C) := FiniteDimensional.complete ℂ (V × C)
  have hd := AlgebraicGeometry.ComplexPoints.Analytic.ImmersionNormalForm.hasFDerivAt_immersionExtension f C (fderiv ℂ f x) x
    ((hf x hx).differentiableAt (hU.mem_nhds hx)).hasFDerivAt
  have heq : (fderiv ℂ f x).comp (ContinuousLinearMap.fst ℂ V C) +
      C.subtypeL.comp (ContinuousLinearMap.snd ℂ V C) = e.toContinuousLinearMap := by
    apply ContinuousLinearMap.ext
    intro z
    exact (he z).symm
  rw [heq] at hd
  have hg := AlgebraicGeometry.ComplexPoints.Analytic.ImmersionNormalForm.contDiffAt_immersionExtension f C x hf1
  let q₀ := hg.toOpenPartialHomeomorph (AlgebraicGeometry.ComplexPoints.Analytic.ImmersionNormalForm.immersionExtension f C) hd (by norm_num)
  have hx₀ : (x, (0 : C)) ∈ q₀.source :=
    hg.mem_toOpenPartialHomeomorph_source hd (by norm_num)
  have hi₀ : ContDiffAt ℂ 1 q₀.symm (q₀ (x, 0)) := hg.to_localInverse hd (by norm_num)
  let q := q₀.restrContDiff ℂ 1 (by norm_num)
  have hxq : (x, (0 : C)) ∈ q.source := ⟨hx₀, hg, hi₀⟩
  have hzero : ∀ y, q (y, 0) = f y := by
    intro y
    change f y + ((0 : C) : W) = f y
    simp
  have hqi : DifferentiableOn ℂ q.symm q.target :=
    (q₀.contDiffOn_restrContDiff_target ℂ (by norm_num : (1 : ℕ∞ω) ≠ ∞)).differentiableOn
      (by norm_num)
  refine ⟨C, q, hxq, hzero, hqi, ?_⟩
  intro y hy
  constructor
  · intro hz
    have hp : ((q.symm y).1, (0 : C)) = q.symm y := Prod.ext rfl hz.symm
    refine ⟨(q.symm y).1, hp ▸ q.map_target hy, ?_⟩
    rw [← hzero, hp, q.right_inv hy]
  · rintro ⟨z, hz, hzy⟩
    rw [← hzy, ← hzero z, q.left_inv hz]

omit [FiniteDimensional ℂ V] in
/-- Each normal chart gives actual finitely many complex-valued holomorphic equations. -/
theorem local_equations_of_normal_chart {f : V → W} {x : V}
    (h : HasHolomorphicNormalChart f x) :
    ∃ (k : ℕ) (O : Set W) (g : W → (Fin k → ℂ)) (D : Set V),
      IsOpen O ∧ f x ∈ O ∧ IsOpen D ∧ x ∈ D ∧
      DifferentiableOn ℂ g O ∧ ∀ y ∈ O, g y = 0 ↔ ∃ z ∈ D, f z = y := by
  obtain ⟨C, q, hx, hzero, hqi, heq⟩ := h
  let k := Module.finrank ℂ C
  let e : C ≃L[ℂ] (Fin k → ℂ) :=
    ContinuousLinearEquiv.ofFinrankEq (Module.finrank_fin_fun ℂ).symm
  let g : W → (Fin k → ℂ) := fun y => e (q.symm y).2
  let D : Set V := (fun z : V => (z, (0 : C))) ⁻¹' q.source
  have hD : IsOpen D := q.open_source.preimage (continuous_id.prodMk continuous_const)
  refine ⟨k, q.target, g, D, q.open_target, ?_, hD, hx, ?_, ?_⟩
  · rw [← hzero x]
    exact q.map_source hx
  · exact e.differentiable.comp_differentiableOn (differentiable_snd.comp_differentiableOn hqi)
  · intro y hy
    change e (q.symm y).2 = 0 ↔ _
    rw [map_eq_zero_iff _ e.injective]
    exact heq y hy

omit [FiniteDimensional ℂ V] in
/-- Normal coordinates may be confined to any prescribed open parameter neighborhood. -/
theorem local_equations_in_neighborhood {f : V → W} {x : V}
    (h : HasHolomorphicNormalChart f x) {U : Set V} (hU : IsOpen U) (hxU : x ∈ U) :
    ∃ (k : ℕ) (O : Set W) (g : W → (Fin k → ℂ)) (D : Set V),
      IsOpen O ∧ f x ∈ O ∧ IsOpen D ∧ x ∈ D ∧ D ⊆ U ∧
      DifferentiableOn ℂ g O ∧ ∀ y ∈ O, g y = 0 ↔ ∃ z ∈ D, f z = y := by
  obtain ⟨C, q, hx, hzero, hqi, _⟩ := h
  let q' := q.restrOpen (Prod.fst ⁻¹' U) (hU.preimage continuous_fst)
  have hx' : (x, (0 : C)) ∈ q'.source := ⟨hx, hxU⟩
  let k := Module.finrank ℂ C
  let e : C ≃L[ℂ] (Fin k → ℂ) :=
    ContinuousLinearEquiv.ofFinrankEq (Module.finrank_fin_fun ℂ).symm
  let g : W → (Fin k → ℂ) := fun y => e (q'.symm y).2
  let D : Set V := (fun z : V => (z, (0 : C))) ⁻¹' q'.source
  have hD : IsOpen D := q'.open_source.preimage (continuous_id.prodMk continuous_const)
  have hz' : ∀ z, q' (z, 0) = f z := hzero
  refine ⟨k, q'.target, g, D, q'.open_target, ?_, hD, hx', fun z hz => hz.2, ?_, ?_⟩
  · rw [← hz' x]
    exact q'.map_source hx'
  · exact e.differentiable.comp_differentiableOn
      (differentiable_snd.comp_differentiableOn (hqi.mono (fun y hy => hy.1)))
  · intro y hy
    change e (q'.symm y).2 = 0 ↔ _
    rw [map_eq_zero_iff _ e.injective]
    constructor
    · intro hz
      have hp : ((q'.symm y).1, (0 : C)) = q'.symm y := Prod.ext rfl hz.symm
      refine ⟨(q'.symm y).1, hp ▸ q'.map_target hy, ?_⟩
      rw [← hz', hp, q'.right_inv hy]
    · rintro ⟨z, hz, hzy⟩
      rw [← hzy, ← hz' z, q'.left_inv hz]

omit [FiniteDimensional ℂ V] in
/-- An open quotient parametrization and an actual embedding turn the local
parameter equations into equations for the full image in an affine chart. -/
theorem local_equations_for_embedded_image
    {T P : Type*} [TopologicalSpace T] [TopologicalSpace P]
    (p : V → T) (hp : Continuous p) (hpo : IsOpenMap p)
    (f : T → P) (hf : Topology.IsEmbedding f)
    (e : OpenPartialHomeomorph P W) (he : e.target = univ)
    (x : V) (hx : f (p x) ∈ e.source)
    (hn : HasHolomorphicNormalChart (fun z => e (f (p z))) x) :
    ∃ (k : ℕ) (O : Set W) (g : W → (Fin k → ℂ)),
      IsOpen O ∧ e (f (p x)) ∈ O ∧ DifferentiableOn ℂ g O ∧
      ∀ y ∈ O, g y = 0 ↔ e.symm y ∈ range f := by
  let U : Set V := (f ∘ p) ⁻¹' e.source
  have hU : IsOpen U := e.open_source.preimage (hf.continuous.comp hp)
  obtain ⟨k, O, g, D, hO, hxO, hD, hxD, hDU, hg, hgeq⟩ :=
    local_equations_in_neighborhood hn hU hx
  obtain ⟨B, hB, hpre⟩ := hf.isInducing.isOpen_iff.mp (hpo D hD)
  have hxi : f (p x) ∈ B := by
    change p x ∈ f ⁻¹' B
    rw [hpre]
    exact ⟨x, hxD, rfl⟩
  have hei : Continuous e.symm := by
    apply continuousOn_univ.mp
    simpa only [he] using e.continuousOn_symm
  refine ⟨k, O ∩ e.symm ⁻¹' B, g, hO.inter (hB.preimage hei),
    ⟨hxO, by simpa only [mem_preimage, e.left_inv hx] using hxi⟩,
    hg.mono inter_subset_left, ?_⟩
  intro y hy
  rw [hgeq y hy.1]
  constructor
  · rintro ⟨z, hz, hzy⟩
    refine ⟨p z, ?_⟩
    rw [← hzy]
    exact (e.left_inv (hDU hz)).symm
  · rintro ⟨t, ht⟩
    have htD : t ∈ p '' D := by
      rw [← hpre]
      change f t ∈ B
      rw [ht]
      exact hy.2
    obtain ⟨z, hz, hzt⟩ := htD
    refine ⟨z, hz, ?_⟩
    rw [hzt, ht, e.right_inv (by rw [he]; trivial)]

/-- The projective embedding of the CM torus has holomorphic local normal
charts in every standard affine patch, using only the named RiemannProjectivity input. -/
theorem projective_period_torus_normal_charts
    (Φ : Data.CM.ProjectivePeriodData) :
    ∃ (n : ℕ) (f : Φ.periodTorus → Projectivization ℂ (Fin (n + 1) → ℂ)),
      Topology.IsClosedEmbedding f ∧
      ∀ (z : Φ.space) (i : Fin (n + 1)),
        AlgebraicGeometry.Foundations.Scheme.ProjectiveCoordinatesIn.Algebraic.ProjectiveCoordinates.InPatch i (f (QuotientAddGroup.mk z)) →
        HasHolomorphicNormalChart
          (fun w => AlgebraicGeometry.ComplexPoints.Analytic.ProjectiveCharts.projectiveFinChart i (f (QuotientAddGroup.mk w))) z := by
  obtain ⟨n, f, hf, hd⟩ := Root.CM.Algebraization.projective_period_torus_all_charts Φ
  refine ⟨n, f, hf, ?_⟩
  intro z i hi
  let U : Set (Φ.space) := {w | AlgebraicGeometry.Foundations.Scheme.ProjectiveCoordinatesIn.Algebraic.ProjectiveCoordinates.InPatch i (f (QuotientAddGroup.mk w))}
  have hU : IsOpen U := (AlgebraicGeometry.ComplexPoints.Analytic.ProjectiveCharts.isOpen_projectivePatch i).preimage
    (hf.continuous.comp QuotientAddGroup.continuous_mk)
  exact hasHolomorphicNormalChart_of_injective_fderiv _ z hU hi
    (fun w hw => (hd w i hw).1.differentiableWithinAt) (hd z i hi).2

/-- The full projective image has finite local holomorphic equations in
every standard affine chart at every image point. -/
theorem projective_period_torus_image_equations
    (Φ : Data.CM.ProjectivePeriodData) :
    ∃ (n : ℕ) (f : Φ.periodTorus → Projectivization ℂ (Fin (n + 1) → ℂ)),
      Topology.IsClosedEmbedding f ∧
      ∀ (t : Φ.periodTorus) (i : Fin (n + 1)), AlgebraicGeometry.Foundations.Scheme.ProjectiveCoordinatesIn.Algebraic.ProjectiveCoordinates.InPatch i (f t) →
        ∃ (k : ℕ) (O : Set (Fin n → ℂ)) (g : (Fin n → ℂ) → (Fin k → ℂ)),
          IsOpen O ∧ AlgebraicGeometry.ComplexPoints.Analytic.ProjectiveCharts.projectiveFinChart i (f t) ∈ O ∧ DifferentiableOn ℂ g O ∧
          ∀ y ∈ O, g y = 0 ↔ (AlgebraicGeometry.ComplexPoints.Analytic.ProjectiveCharts.projectiveFinChart i).symm y ∈ range f := by
  obtain ⟨n, f, hf, hn⟩ := projective_period_torus_normal_charts Φ
  refine ⟨n, f, hf, ?_⟩
  intro t i hi
  obtain ⟨z, rfl⟩ := QuotientAddGroup.mk_surjective t
  exact local_equations_for_embedded_image
    (QuotientAddGroup.mk : Φ.space → Φ.periodTorus)
    QuotientAddGroup.continuous_mk QuotientAddGroup.isOpenMap_coe f hf.isEmbedding
    (AlgebraicGeometry.ComplexPoints.Analytic.ProjectiveCharts.projectiveFinChart i) (AlgebraicGeometry.ComplexPoints.Analytic.ProjectiveCharts.projectiveFinChart_target i) z hi (hn z i hi)

end

end OAI.RepresentationTheory.Theta.Geometric.Torus.TorusImageCharts.CM.Algebraization.ImageCharts

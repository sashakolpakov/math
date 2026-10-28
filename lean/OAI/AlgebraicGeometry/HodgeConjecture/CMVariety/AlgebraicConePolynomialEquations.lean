import OAI.AlgebraicGeometry.HodgeConjecture.CMVariety.AlgebraicCone
import OAI.AlgebraicGeometry.HodgeConjecture.CMVariety.AlgebraicConeDensePreimage
import OAI.Geometry.ComplexTorus.RiemannProjectivity.ParameterEquationsOn
import OAI.Geometry.ComplexTorus.RiemannProjectivity.LocalFiber

/-! # Algebraic Cone Polynomial Equations -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.CMVariety.AlgebraicConePolynomialEquations.CM.Abelian.Algebraization.ConePolynomialEquations

noncomputable section

open Set Filter _root_.Polynomial _root_.Metric
open scoped _root_.Topology

variable {n : ℕ}

theorem vanishes_on_cone (Φ : ProjectiveTorusData.CM.Abelian.ProjectivePeriodData)
    (f : Φ.periodTorus → Projectivization ℂ (Fin (n + 1) → ℂ)) (hf : Topology.IsEmbedding f)
    (hd : ∀ (z : Φ.space) (i : Fin (n + 1)),
      f (QuotientAddGroup.mk z) ∈ (ComplexPoints.Analytic.ProjectiveCharts.projectiveFinChart i).source →
      DifferentiableAt ℂ (fun w => ComplexPoints.Analytic.ProjectiveCharts.projectiveFinChart i (f (QuotientAddGroup.mk w))) z)
    (L : (Fin (n + 1) → ℂ) →L[ℂ] (Fin (Module.finrank ℂ (Φ.space) + 1) → ℂ))
    (hfinite : ∀ y, {w | w ∈ ComplexGroups.HolomorphicAlgebraicity.ProjectiveCone.Constructions.Cone.projectiveCone (range f) ∧ L w = y}.Finite)
    (l : (Fin (n + 1) → ℂ) →L[ℂ] ℂ)
    (P : (Fin (Module.finrank ℂ (Φ.space) + 1) → ℂ) → ℂ[X])
    (k : ℕ) (hdeg : ∀ y, (P y).natDegree ≤ k)
    {O D : Set (Fin (Module.finrank ℂ (Φ.space) + 1) → ℂ)}
    (hO : IsOpen O) (hD : O ⊆ closure D)
    (hcoeff : ∀ j, DifferentiableOn ℂ (fun y => (P y).coeff j) O)
    {B : Set ℂ} (hB : IsOpen B)
    (hzero : ∀ w ∈ ComplexGroups.HolomorphicAlgebraicity.ProjectiveCone.Constructions.Cone.projectiveCone (range f), L w ∈ O → L w ∈ D → l w ∈ B →
      (P (L w)).eval (l w) = 0)
    {v : Fin (n + 1) → ℂ} (hv : v ∈ ComplexGroups.HolomorphicAlgebraicity.ProjectiveCone.Constructions.Cone.projectiveCone (range f)) (hv0 : v ≠ 0)
    (hbase : L v ∈ O) (hvert : l v ∈ B) : (P (L v)).eval (l v) = 0 := by
  let A := L ⁻¹' O ∩ l ⁻¹' B
  have hA : IsOpen A := (hO.preimage L.continuous).inter (hB.preimage l.continuous)
  have hvA : v ∈ A := ⟨hbase, hvert⟩
  have hclosure := AlgebraicConeDensePreimage.CM.Abelian.Algebraization.ConeDensePreimage.mem_closure_preimage Φ f hf hd L hfinite hO hD hv hv0 hbase
  have hcl : v ∈ closure (A ∩ {w | w ∈ ComplexGroups.HolomorphicAlgebraicity.ProjectiveCone.Constructions.Cone.projectiveCone (range f) ∧ L w ∈ D}) :=
    hA.inter_closure ⟨hvA, hclosure⟩
  have hdG := Geometry.ComplexTorus.RiemannProjectivity.ParameterEquationsOn.Constructions.ParameterEquations.differentiableOn_eval k hdeg hcoeff
    L.differentiable.differentiableOn l.differentiable.differentiableOn
    (show MapsTo L A O from fun _ hw => hw.1)
  have hmem : (P (L v)).eval (l v) ∈ closure ({0} : Set ℂ) :=
    ((hdG.continuousOn v hvA).mono inter_subset_left).mem_closure hcl
      (fun w hw => hzero w hw.2.1 hw.1.1 hw.2.2 hw.1.2)
  simpa only [closure_singleton, mem_singleton_iff] using hmem

theorem local_equation_of_coordinate_image (Φ : ProjectiveTorusData.CM.Abelian.ProjectivePeriodData)
    (f : Φ.periodTorus → Projectivization ℂ (Fin (n + 1) → ℂ)) (hf : Topology.IsEmbedding f)
    (hd : ∀ (z : Φ.space) (i : Fin (n + 1)),
      f (QuotientAddGroup.mk z) ∈ (ComplexPoints.Analytic.ProjectiveCharts.projectiveFinChart i).source →
      DifferentiableAt ℂ (fun w => ComplexPoints.Analytic.ProjectiveCharts.projectiveFinChart i (f (QuotientAddGroup.mk w))) z)
    (L : (Fin (n + 1) → ℂ) →L[ℂ] (Fin (Module.finrank ℂ (Φ.space) + 1) → ℂ))
    (hfinite : ∀ y, {w | w ∈ ComplexGroups.HolomorphicAlgebraicity.ProjectiveCone.Constructions.Cone.projectiveCone (range f) ∧ L w = y}.Finite)
    (l : (Fin (n + 1) → ℂ) →L[ℂ] ℂ)
    (hclosed : IsClosed ((fun v => (L v, l v)) '' ComplexGroups.HolomorphicAlgebraicity.ProjectiveCone.Constructions.Cone.projectiveCone (range f)))
    {x : Fin (Module.finrank ℂ (Φ.space) + 1) → ℂ} (hx0 : x ≠ 0) {z₀ : ℂ}
    (hlocal : ComplexGroups.HolomorphicAlgebraicity.ZeroLocus.Constructions.Cone.HolomorphicZeroSetAt
      ((fun v => (L v, l v)) '' ComplexGroups.HolomorphicAlgebraicity.ProjectiveCone.Constructions.Cone.projectiveCone (range f)) (x, z₀)) :
    ∃ (R : ℝ) (k : ℕ) (U : Set (Fin (Module.finrank ℂ (Φ.space) + 1) → ℂ))
        (P : (Fin (Module.finrank ℂ (Φ.space) + 1) → ℂ) → ℂ[X])
        (c : (Fin (Module.finrank ℂ (Φ.space) + 1) → ℂ) → ℂ),
      0 < R ∧ IsOpen U ∧ x ∈ U ∧ DifferentiableOn ℂ c U ∧
      U ⊆ closure {y | y ∈ U ∧ c y ≠ 0} ∧
      (∀ j, DifferentiableOn ℂ (fun y => (P y).coeff j) U) ∧
      (∀ y, (P y).Monic ∧ (P y).natDegree = k) ∧
      (∀ y ∈ U, ∀ z, (P y).eval z = 0 →
        (y, z) ∈ (fun v => (L v, l v)) '' ComplexGroups.HolomorphicAlgebraicity.ProjectiveCone.Constructions.Cone.projectiveCone (range f)) ∧
      (∀ y ∈ U, c y ≠ 0 → (P y).Separable) ∧
      ∀ y ∈ U, ∀ z ∈ ball z₀ R,
        (y, z) ∈ (fun v => (L v, l v)) '' ComplexGroups.HolomorphicAlgebraicity.ProjectiveCone.Constructions.Cone.projectiveCone (range f) ↔ (P y).eval z = 0 := by
  have hfin : {z : ℂ | (x, z) ∈
      (fun v => (L v, l v)) '' ComplexGroups.HolomorphicAlgebraicity.ProjectiveCone.Constructions.Cone.projectiveCone (range f)}.Finite := by
    apply ((hfinite x).image l).subset
    rintro z ⟨v, hv, hp⟩
    exact ⟨v, ⟨hv, congrArg Prod.fst hp⟩, congrArg Prod.snd hp⟩
  obtain ⟨R, k, U, P, c, hR, hU, hxU, hc, hdense, hcoeff, hP, hroot, heq⟩ :=
    Geometry.ComplexTorus.RiemannProjectivity.LocalFiber.Constructions.LocalFiberExtension.exists_separable_extended_equation hclosed hlocal hfin
  let W := U ∩ {y | y ≠ 0}
  have hW : IsOpen W := hU.inter isOpen_compl_singleton
  have hdenseW : W ⊆ closure {y | y ∈ W ∧ c y ≠ 0} := by
    intro y hy
    apply mem_closure_iff_frequently.mpr
    exact ((mem_closure_iff_frequently.mp (hdense hy.1)).and_eventually
      (hW.mem_nhds hy)).mono (fun _ hz => ⟨hz.2, hz.1.2⟩)
  refine ⟨R, k, W, P, c, hR, hW, ⟨hxU, hx0⟩, hc.mono inter_subset_left, hdenseW,
    fun j => (hcoeff j).mono inter_subset_left, hP,
    fun y hy => hroot y hy.1, fun y hy hcy => (heq y hy.1 hcy).1, ?_⟩
  intro y hy z hz
  constructor
  · rintro ⟨v, hv, hp⟩
    have hvy : L v = y := congrArg Prod.fst hp
    have hvz : l v = z := congrArg Prod.snd hp
    have hv0 : v ≠ 0 := by
      intro hvzero
      exact hy.2 (by rw [← hvy, hvzero, map_zero])
    have hzero : (P (L v)).eval (l v) = 0 :=
      vanishes_on_cone Φ f hf hd L hfinite l P k (fun y => (hP y).2.le)
        hU hdense hcoeff isOpen_ball
        (fun w hw hwU hwD hwB => ((heq (L w) hwU hwD.2).2 (l w)
          (ball_subset_closedBall hwB)).mp ⟨w, hw, rfl⟩)
        hv hv0 (by simpa only [hvy] using hy.1) (by simpa only [hvz] using hz)
    simpa only [hvy, hvz] using hzero
  · exact hroot y hy.1 z

end

end OAI.AlgebraicGeometry.HodgeConjecture.CMVariety.AlgebraicConePolynomialEquations.CM.Abelian.Algebraization.ConePolynomialEquations

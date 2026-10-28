import OAI.Geometry.ComplexTorus.RiemannProjectivity.FiniteRemovabilityOn
import OAI.AlgebraicGeometry.ComplexGroups.HolomorphicAlgebraicity.Moments

/-! # Cauchy Extension On -/

namespace OAI.Geometry.ComplexTorus.RiemannProjectivity.CauchyExtensionOn.Constructions.CauchyExtension

noncomputable section

/-!
# RiemannProjectivity: a holomorphic Cauchy extension through branch equations

On a product neighborhood with a zero-free vertical boundary, a bounded
holomorphic function off a holomorphic zero locus extends by a contour
integral. The extended function is jointly holomorphic and keeps its bound.
-/

open Set Filter _root_.Metric _root_.Complex
open scoped _root_.Topology

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V] [FiniteDimensional ℂ V]

def transform (f : V × ℂ → ℂ) (c : ℂ) (R : ℝ) (p : V × ℂ) : ℂ :=
  (2 * Real.pi * I : ℂ)⁻¹ * ∮ z in C(c, R), (z - p.2)⁻¹ * f (p.1, z)

theorem differentiableOn_transform {f : V × ℂ → ℂ} {O : Set (V × ℂ)}
    (hO : IsOpen O) (hf : DifferentiableOn ℂ f O) {A : Set V} (hA : IsOpen A)
    {c : ℂ} {R : ℝ} (hR : 0 < R) (hAO : A ×ˢ sphere c R ⊆ O) :
    DifferentiableOn ℂ (transform f c R) (A ×ˢ ball c R) := by
  let N : (V × ℂ) × ℂ → V × ℂ := fun p => (p.1.1, p.2)
  let D : (V × ℂ) × ℂ → ℂ := fun p => p.2 - p.1.2
  have hN : Differentiable ℂ N := (differentiable_fst.comp differentiable_fst).prodMk differentiable_snd
  have hD : Differentiable ℂ D := differentiable_snd.sub (differentiable_snd.comp differentiable_fst)
  let B := N ⁻¹' O ∩ {p | D p ≠ 0}
  have hB : IsOpen B := (hO.preimage hN.continuous).inter
    (isOpen_ne_fun hD.continuous continuous_const)
  let F : (V × ℂ) × ℂ → ℂ := fun p => (D p)⁻¹ * f (N p)
  have hF : DifferentiableOn ℂ F B :=
    (hD.differentiableOn.fun_inv (fun p hp => hp.2)).fun_mul
      ((hf.comp hN.differentiableOn (mapsTo_preimage N O)).mono inter_subset_left)
  have hAB : (A ×ˢ ball c R) ×ˢ sphere c R ⊆ B := by
    intro p hp
    refine ⟨hAO ⟨hp.1.1, hp.2⟩, ?_⟩
    change p.2 - p.1.2 ≠ 0
    intro h
    have he := sub_eq_zero.mp h
    have hr := mem_sphere.mp hp.2
    rw [he] at hr
    exact (ne_of_lt (mem_ball.mp hp.1.2)) hr
  intro p hp
  have h := AlgebraicGeometry.ComplexGroups.HolomorphicAlgebraicity.ParametricIntegralAt.Constructions.ParametricIntegral.differentiableAt_weighted_circleIntegral
    hB hF (hA.prod isOpen_ball) hp hR.le hAB
    (w := fun _ => 1) continuousOn_const
  have hd : DifferentiableAt ℂ (fun q => ∮ z in C(c, R), (z - q.2)⁻¹ * f (q.1, z)) p := by
    simpa only [one_mul] using h
  exact (hd.const_mul _).differentiableWithinAt

theorem finite_disk_zeros {g : ℂ → ℂ} {c : ℂ} {R : ℝ} (hR : 0 < R)
    (hg : AnalyticOnNhd ℂ g (closedBall c R))
    (hboundary : ∀ z ∈ sphere c R, g z ≠ 0) :
    {z : ℂ | z ∈ closedBall c R ∧ g z = 0}.Finite := by
  obtain ⟨P, hP, _, u, _, hu, heq⟩ := AlgebraicGeometry.ComplexGroups.HolomorphicAlgebraicity.ClosedDiskFactorization.Constructions.DiskFactorization.exists_polynomial_unit_on_closedDisk
    hg (AlgebraicGeometry.ComplexGroups.HolomorphicAlgebraicity.RootFamiliesAt.Constructions.RootFamilies.exists_nonzero_in_ball hR hg.continuousOn hboundary) hboundary
  apply (Polynomial.finite_setOfPred_isRoot hP.ne_zero).subset
  intro z hz
  have h := (heq z hz.1).eq_of_nhds
  rw [hz.2] at h
  exact (mul_eq_zero.mp h.symm).resolve_right (hu z hz.1)

/-- Extension on a vertical tube. The zero-free circle supplies the contour
at every base point; no continuity of selected roots is assumed. -/
theorem bounded_extension_on_tube {f g : V × ℂ → ℂ} {O : Set (V × ℂ)}
    (hO : IsOpen O) (hg : DifferentiableOn ℂ g O)
    (hf : DifferentiableOn ℂ f (O ∩ {p | g p ≠ 0}))
    {A : Set V} (hA : IsOpen A) {c : ℂ} {R : ℝ} (hR : 0 < R)
    (hAO : A ×ˢ closedBall c R ⊆ O)
    (hboundary : ∀ y ∈ A, ∀ z ∈ sphere c R, g (y, z) ≠ 0)
    {C : ℝ} (hbound : ∀ p ∈ O ∩ {p | g p ≠ 0}, ‖f p‖ ≤ C) :
    DifferentiableOn ℂ (transform f c R) (A ×ˢ ball c R) ∧
      EqOn (transform f c R) f ((A ×ˢ ball c R) ∩ {p | g p ≠ 0}) ∧
      ∀ p ∈ A ×ˢ ball c R, ‖transform f c R p‖ ≤ C := by
  have hD : IsOpen (O ∩ {p | g p ≠ 0}) :=
    hg.continuousOn.isOpen_inter_preimage hO isOpen_compl_singleton
  have hd := differentiableOn_transform hD hf hA hR
    (fun p hp => ⟨hAO ⟨hp.1, sphere_subset_closedBall hp.2⟩, hboundary p.1 hp.1 p.2 hp.2⟩)
  have hdata (y : V) (hy : y ∈ A) :
      ∃ K : Set ℂ, K.Finite ∧ K ⊆ ball c R ∧
        (∀ z ∈ closedBall c R, z ∉ K ↔ g (y, z) ≠ 0) ∧
        DifferentiableOn ℂ (fun z => f (y, z)) (closedBall c R \ K) ∧
        ∀ z ∈ closedBall c R \ K, ‖f (y, z)‖ ≤ C := by
    let K := {z : ℂ | z ∈ closedBall c R ∧ g (y, z) = 0}
    have hgs : AnalyticOnNhd ℂ (fun z => g (y, z)) (closedBall c R) := by
      have hs := hg.comp ((differentiable_const y).prodMk differentiable_id).differentiableOn
        (mapsTo_preimage (fun z : ℂ => (y, z)) O)
      exact (hs.analyticOnNhd (hO.preimage (continuous_const.prodMk continuous_id))).mono
        (fun z hz => hAO ⟨hy, hz⟩)
    have hKfin : K.Finite := finite_disk_zeros hR hgs (hboundary y hy)
    have hKint : K ⊆ ball c R := by
      intro z hz
      apply lt_of_le_of_ne (mem_closedBall.mp hz.1)
      intro he
      exact hboundary y hy z (mem_sphere.mpr he) hz.2
    have hKeq : ∀ z ∈ closedBall c R, z ∉ K ↔ g (y, z) ≠ 0 := by
      intro z hz
      simp only [K, mem_ofPred_eq, hz, true_and]
    have hmap : MapsTo (fun z : ℂ => (y, z)) (closedBall c R \ K) (O ∩ {p | g p ≠ 0}) :=
      fun z hz => ⟨hAO ⟨hy, hz.1⟩, (hKeq z hz.1).mp hz.2⟩
    exact ⟨K, hKfin, hKint, hKeq,
      hf.comp ((differentiable_const y).prodMk differentiable_id).differentiableOn hmap,
      fun z hz => hbound (y, z) (hmap hz)⟩
  refine ⟨hd, ?_, ?_⟩
  · intro p hp
    obtain ⟨K, hK, hKi, hKeq, hfs, hbs⟩ := hdata p.1 hp.1.1
    exact FiniteRemovabilityOn.Constructions.FiniteRemovability.cauchy_formula_off_finite hK hR hKi hfs hbs hp.1.2
      ((hKeq p.2 (ball_subset_closedBall hp.1.2)).mpr hp.2)
  · intro p hp
    obtain ⟨K, hK, hKi, _, hfs, hbs⟩ := hdata p.1 hp.1
    change ‖(2 * Real.pi * I : ℂ)⁻¹ * (∮ z in C(c, R), (z - p.2)⁻¹ * f (p.1, z))‖ ≤ C
    rw [FiniteRemovabilityOn.Constructions.FiniteRemovability.cauchy_formula_fill hK hR hKi hfs hbs hp.2]
    exact FiniteRemovabilityOn.Constructions.FiniteRemovability.norm_fill_le hK isOpen_ball
      (hfs.mono (sdiff_subset_sdiff_left ball_subset_closedBall))
      (fun z hz => hbs z ⟨ball_subset_closedBall hz.1, hz.2⟩) hp.2

end

end OAI.Geometry.ComplexTorus.RiemannProjectivity.CauchyExtensionOn.Constructions.CauchyExtension

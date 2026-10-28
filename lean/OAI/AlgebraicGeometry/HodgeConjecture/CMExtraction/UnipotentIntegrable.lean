import OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.UnipotentCosetIntegral
import OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.HeightFibers

/-! # Unipotent Integrable -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.UnipotentIntegrable.Iwasawa

noncomputable section

section

/-! Integrability of the individual coset indicators in each successive
unipotent coordinate, including cosets outside the chosen height fibre. -/

open scoped Classical
open _root_.MeasureTheory

variable (q : ℕ) [Fact q.Prime] [MeasurableSpace ℚ_[q]] [BorelSpace ℚ_[q]]
  (μ : Measure ℚ_[q]) [μ.IsAddLeftInvariant]
  (hO : MeasurableSet (Unipotent.Iwasawa.padicIntegralSet q)) (hvol : μ (Unipotent.Iwasawa.padicIntegralSet q) = 1)

include hO hvol in
theorem padic_integrable_translated_indicator (c : ℚ_[q]) (r : ℂ) :
    Integrable (fun x => if x - c ∈ Unipotent.Iwasawa.padicIntegralSet q then r else 0) μ := by
  let S := (fun x : ℚ_[q] => x - c) ⁻¹' Unipotent.Iwasawa.padicIntegralSet q
  have hS : MeasurableSet S := hO.preimage (measurable_id.sub_const c)
  have hm : μ S = 1 := by
    dsimp [S]
    rw [show (fun x : ℚ_[q] => x - c) = (fun x => -c + x) by funext x; ring]
    rw [measure_preimage_add, hvol]
  have hi : IntegrableOn (fun _ : ℚ_[q] => r) S μ := integrableOn_const (by rw [hm]; simp)
  exact (hi.integrable_indicator hS).congr (Filter.Eventually.of_forall (fun _ => rfl))

def gl3UnipotentKernelIntegrable (ell : Fin 3 → ℤ)
    (f : RepresentationTheory.Satake.GL3TorusIwasawa.Iwasawa.CosetModule (RepresentationTheory.Theta.Geometric.SphericalGU.Spherical.integralGL3 q)) : Prop :=
  (∀ a c : ℚ_[q], Integrable (fun b =>
    f (QuotientGroup.mk (HeightFibers.Iwasawa.gl3Torus q ell * Unipotent.Iwasawa.gl3Unipotent a b c))) μ) ∧
  (∀ a : ℚ_[q], Integrable (fun c => ∫ b,
    f (QuotientGroup.mk (HeightFibers.Iwasawa.gl3Torus q ell * Unipotent.Iwasawa.gl3Unipotent a b c)) ∂μ) μ) ∧
  Integrable (fun a => ∫ c, ∫ b,
    f (QuotientGroup.mk (HeightFibers.Iwasawa.gl3Torus q ell * Unipotent.Iwasawa.gl3Unipotent a b c)) ∂μ ∂μ) μ

include hO hvol in
theorem gl3Unipotent_single_integrable (ell : Fin 3 → ℤ)
    (c : RepresentationTheory.Theta.Geometric.SphericalGU.Spherical.GL3 q ⧸ RepresentationTheory.Theta.Geometric.SphericalGU.Spherical.integralGL3 q) (r : ℂ) :
    gl3UnipotentKernelIntegrable q μ ell (Finsupp.single c r) := by
  by_cases hc : (Iwasawa.gl3Decomposition q).height c = ell
  · obtain ⟨x, y, z, rfl⟩ := (HeightFibers.Iwasawa.gl3_height_fiber q ell c).mp hc
    have hinner (a d : ℚ_[q]) :
        (∫ b, Finsupp.single (QuotientGroup.mk (HeightFibers.Iwasawa.gl3Torus q ell * Unipotent.Iwasawa.gl3Unipotent x y z) :
          RepresentationTheory.Theta.Geometric.SphericalGU.Spherical.GL3 q ⧸ RepresentationTheory.Theta.Geometric.SphericalGU.Spherical.integralGL3 q) r
          (QuotientGroup.mk (HeightFibers.Iwasawa.gl3Torus q ell * Unipotent.Iwasawa.gl3Unipotent a b d)) ∂μ) =
        if a - x ∈ Unipotent.Iwasawa.padicIntegralSet q ∧ d - z ∈ Unipotent.Iwasawa.padicIntegralSet q then r else 0 := by
      simpa only [Finsupp.single_apply] using
        UnipotentCosetIntegral.Iwasawa.gl3Unipotent_coset_inner_integral q μ hO hvol (HeightFibers.Iwasawa.gl3Torus q ell) x y z a d r
    have hmiddle (a : ℚ_[q]) :
        (∫ d, ∫ b, Finsupp.single (QuotientGroup.mk (HeightFibers.Iwasawa.gl3Torus q ell * Unipotent.Iwasawa.gl3Unipotent x y z) :
          RepresentationTheory.Theta.Geometric.SphericalGU.Spherical.GL3 q ⧸ RepresentationTheory.Theta.Geometric.SphericalGU.Spherical.integralGL3 q) r
          (QuotientGroup.mk (HeightFibers.Iwasawa.gl3Torus q ell * Unipotent.Iwasawa.gl3Unipotent a b d)) ∂μ ∂μ) =
        if a - x ∈ Unipotent.Iwasawa.padicIntegralSet q then r else 0 := by
      simpa only [Finsupp.single_apply] using
        UnipotentCosetIntegral.Iwasawa.gl3Unipotent_coset_middle_integral q μ hO hvol (HeightFibers.Iwasawa.gl3Torus q ell) x y z a r
    refine ⟨?_, ?_, ?_⟩
    · intro a d
      simp only [Finsupp.single_apply, Unipotent.Iwasawa.gl3Unipotent_coset_iff]
      have he (b : ℚ_[q]) : b - y - x * (d - z) = b - (y + x * (d - z)) := by ring
      simp_rw [he]
      by_cases ha : a - x ∈ Unipotent.Iwasawa.padicIntegralSet q <;> by_cases hd : d - z ∈ Unipotent.Iwasawa.padicIntegralSet q
      · simpa only [ha, hd, true_and, and_true] using
          padic_integrable_translated_indicator q μ hO hvol (y + x * (d - z)) r
      · simp [ha, hd]
      · simp [ha, hd]
      · simp [ha, hd]
    · intro a
      simp_rw [hinner]
      by_cases ha : a - x ∈ Unipotent.Iwasawa.padicIntegralSet q
      · simpa only [ha, true_and] using padic_integrable_translated_indicator q μ hO hvol z r
      · simp [ha]
    · simp_rw [hmiddle]
      exact padic_integrable_translated_indicator q μ hO hvol x r
  · have hzero (a b d : ℚ_[q]) : Finsupp.single c r
        (QuotientGroup.mk (HeightFibers.Iwasawa.gl3Torus q ell * Unipotent.Iwasawa.gl3Unipotent a b d)) = 0 := by
      apply Finsupp.single_eq_of_ne
      intro he
      apply hc
      rw [← he]
      exact HeightFibers.Iwasawa.gl3Torus_unipotent_height q ell a b d
    constructor
    · intro a d; simp_rw [hzero]; exact integrable_zero _ _ _
    · constructor
      · intro a; simp_rw [hzero, integral_zero]; exact integrable_zero _ _ _
      · simp_rw [hzero, integral_zero]; exact integrable_zero _ _ _

end

/-! The actual finite Iwasawa kernel pushforward equals the iterated
unipotent integral. Every exchange with addition uses proved integrability. -/

open scoped Classical
open _root_.MeasureTheory

variable (q : ℕ) [Fact q.Prime] [MeasurableSpace ℚ_[q]] [BorelSpace ℚ_[q]]
  (μ : Measure ℚ_[q]) [μ.IsAddLeftInvariant]
  (hO : MeasurableSet (Unipotent.Iwasawa.padicIntegralSet q)) (hvol : μ (Unipotent.Iwasawa.padicIntegralSet q) = 1)

def gl3UnipotentKernelIntegral (ell : Fin 3 → ℤ)
    (f : RepresentationTheory.Satake.GL3TorusIwasawa.Iwasawa.CosetModule (RepresentationTheory.Theta.Geometric.SphericalGU.Spherical.integralGL3 q)) : ℂ :=
  ∫ a, ∫ c, ∫ b, f (QuotientGroup.mk (HeightFibers.Iwasawa.gl3Torus q ell * Unipotent.Iwasawa.gl3Unipotent a b c)) ∂μ ∂μ ∂μ

omit [BorelSpace ℚ_[q]] [μ.IsAddLeftInvariant] in
theorem gl3UnipotentKernel_add (ell : Fin 3 → ℤ)
    (f g : RepresentationTheory.Satake.GL3TorusIwasawa.Iwasawa.CosetModule (RepresentationTheory.Theta.Geometric.SphericalGU.Spherical.integralGL3 q))
    (hf : gl3UnipotentKernelIntegrable q μ ell f) (hg : gl3UnipotentKernelIntegrable q μ ell g) :
    gl3UnipotentKernelIntegrable q μ ell (f + g) ∧
      gl3UnipotentKernelIntegral q μ ell (f + g) =
        gl3UnipotentKernelIntegral q μ ell f + gl3UnipotentKernelIntegral q μ ell g := by
  have hinner (a c : ℚ_[q]) :
      (∫ b, (f + g) (QuotientGroup.mk (HeightFibers.Iwasawa.gl3Torus q ell * Unipotent.Iwasawa.gl3Unipotent a b c)) ∂μ) =
        (∫ b, f (QuotientGroup.mk (HeightFibers.Iwasawa.gl3Torus q ell * Unipotent.Iwasawa.gl3Unipotent a b c)) ∂μ) +
        (∫ b, g (QuotientGroup.mk (HeightFibers.Iwasawa.gl3Torus q ell * Unipotent.Iwasawa.gl3Unipotent a b c)) ∂μ) :=
    integral_add (hf.1 a c) (hg.1 a c)
  have hmiddle (a : ℚ_[q]) :
      (∫ c, ∫ b, (f + g) (QuotientGroup.mk (HeightFibers.Iwasawa.gl3Torus q ell * Unipotent.Iwasawa.gl3Unipotent a b c)) ∂μ ∂μ) =
        (∫ c, ∫ b, f (QuotientGroup.mk (HeightFibers.Iwasawa.gl3Torus q ell * Unipotent.Iwasawa.gl3Unipotent a b c)) ∂μ ∂μ) +
        (∫ c, ∫ b, g (QuotientGroup.mk (HeightFibers.Iwasawa.gl3Torus q ell * Unipotent.Iwasawa.gl3Unipotent a b c)) ∂μ ∂μ) := by
    simp_rw [hinner]
    exact integral_add (hf.2.1 a) (hg.2.1 a)
  constructor
  · refine ⟨fun a c => (hf.1 a c).add (hg.1 a c), ?_, ?_⟩
    · intro a
      simp_rw [hinner]
      exact (hf.2.1 a).add (hg.2.1 a)
    · simp_rw [hmiddle]
      exact hf.2.2.add hg.2.2
  · unfold gl3UnipotentKernelIntegral
    simp_rw [hmiddle]
    exact integral_add hf.2.2 hg.2.2

include hO hvol in
theorem gl3UnipotentKernel_single (ell : Fin 3 → ℤ)
    (c : RepresentationTheory.Theta.Geometric.SphericalGU.Spherical.GL3 q ⧸ RepresentationTheory.Theta.Geometric.SphericalGU.Spherical.integralGL3 q) (r : ℂ) :
    gl3UnipotentKernelIntegral q μ ell (Finsupp.single c r) =
      Finsupp.single ((Iwasawa.gl3Decomposition q).height c) r ell := by
  by_cases hc : (Iwasawa.gl3Decomposition q).height c = ell
  · rw [Finsupp.single_apply, ite_eq_left hc]
    obtain ⟨x, y, z, rfl⟩ := (HeightFibers.Iwasawa.gl3_height_fiber q ell c).mp hc
    unfold gl3UnipotentKernelIntegral
    simpa only [Finsupp.single_apply] using
      UnipotentCosetIntegral.Iwasawa.gl3Unipotent_coset_integral q μ hO hvol (HeightFibers.Iwasawa.gl3Torus q ell) x y z r
  · rw [Finsupp.single_apply, ite_eq_right hc]
    have hzero (a b d : ℚ_[q]) : Finsupp.single c r
        (QuotientGroup.mk (HeightFibers.Iwasawa.gl3Torus q ell * Unipotent.Iwasawa.gl3Unipotent a b d)) = 0 := by
      apply Finsupp.single_eq_of_ne
      intro he
      apply hc
      rw [← he]
      exact HeightFibers.Iwasawa.gl3Torus_unipotent_height q ell a b d
    simp only [gl3UnipotentKernelIntegral, hzero, integral_zero]

include hO hvol in
theorem gl3UnipotentKernel_pushforward (ell : Fin 3 → ℤ)
    (f : RepresentationTheory.Satake.GL3TorusIwasawa.Iwasawa.CosetModule (RepresentationTheory.Theta.Geometric.SphericalGU.Spherical.integralGL3 q)) :
    gl3UnipotentKernelIntegrable q μ ell f ∧
      gl3UnipotentKernelIntegral q μ ell f = Finsupp.mapDomain (Iwasawa.gl3Decomposition q).height f ell := by
  induction f using Finsupp.induction_linear with
  | zero =>
    simp [gl3UnipotentKernelIntegrable, gl3UnipotentKernelIntegral]
  | add f g hf hg =>
    obtain ⟨hI, hsum⟩ := gl3UnipotentKernel_add q μ ell f g hf.1 hg.1
    refine ⟨hI, ?_⟩
    rw [hsum, hf.2, hg.2, Finsupp.mapDomain_add, Finsupp.add_apply]
  | single c r =>
    exact ⟨gl3Unipotent_single_integrable q μ hO hvol ell c r,
      by rw [Finsupp.mapDomain_single]; exact gl3UnipotentKernel_single q μ hO hvol ell c r⟩

include hO hvol in
theorem gl3_constantTerm_unipotent (ell : Fin 3 → ℤ)
    (T : RepresentationTheory.Satake.GL3TorusIwasawa.Iwasawa.algebra (RepresentationTheory.Theta.Geometric.SphericalGU.Spherical.integralGL3 q)) :
    ((Iwasawa.gl3Decomposition q).constantTerm T).coeff ell =
      gl3UnipotentKernelIntegral q μ ell (RepresentationTheory.Satake.GL3TorusIwasawa.Iwasawa.kernel (RepresentationTheory.Theta.Geometric.SphericalGU.Spherical.integralGL3 q) T) := by
  change ((Iwasawa.gl3Decomposition q).pushforward (RepresentationTheory.Satake.GL3TorusIwasawa.Iwasawa.kernel (RepresentationTheory.Theta.Geometric.SphericalGU.Spherical.integralGL3 q) T)).coeff ell = _
  rw [RepresentationTheory.Satake.GL3TorusIwasawa.Iwasawa.Decomposition.pushforward_coeff]
  exact (gl3UnipotentKernel_pushforward q μ hO hvol ell _).2.symm

end

end OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.UnipotentIntegrable.Iwasawa

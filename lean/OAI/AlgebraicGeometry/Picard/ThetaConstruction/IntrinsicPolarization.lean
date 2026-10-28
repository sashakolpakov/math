import OAI.AlgebraicGeometry.Picard.ThetaConstruction.IntrinsicEndomorphisms
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.RiemannForm

/-! # Intrinsic Polarization -/

namespace OAI.AlgebraicGeometry.Picard.ThetaConstruction.IntrinsicPolarization.Geometric

noncomputable section

/-!
Comparison of an actual polarized abelian variety with the checked ThetaConstruction
analytic data. A polarization is represented by an actual ample algebraic
line bundle. The integral marking records its Chern pairing, rather than
assuming a period comparison. The tangent comparison and quotient lattice
are constructed in the theorem.
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.AbelianUniformizationEq.Constructions.AbelianUniformization
open scoped BigOperators

variable {g : ℕ}

local instance (A : ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety) : IsZLattice ℝ (HodgeConjecture.DegreeTwo.AbelianUniformizationEq.Constructions.AbelianUniformization.periodLattice A) :=
  HodgeConjecture.DegreeTwo.AbelianUniformizationEq.Constructions.AbelianUniformization.periodLattice_full ArithmeticGeometry.Descent.CMVariety.IntrinsicHodgeMaps.Abelian.IntrinsicPeriods.algebraization A

lemma native_tangent_finrank (A : ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety) (b : ArithmeticGeometry.Descent.CMVariety.MarkedAbelianPeriods.IntrinsicPeriods.Marking (DefinitionsIntegral.Index g) A) :
    Module.finrank ℂ (HodgeConjecture.DegreeTwo.Transport.Constructions.AbelianModel A) = g := by
  have hr := Module.finrank_eq_card_basis (b.ofZLatticeBasis ℝ)
  have h := Module.finrank_mul_finrank ℝ ℂ (HodgeConjecture.DegreeTwo.Transport.Constructions.AbelianModel A)
  rw [hr, Complex.finrank_real_complex] at h
  simp only [DefinitionsIntegral.Index, Fintype.card_fin] at h
  omega

/-- Coordinates on the original tangent space, constructed from its dimension. -/
def nativeTangentCoordinates (A : ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety) (b : ArithmeticGeometry.Descent.CMVariety.MarkedAbelianPeriods.IntrinsicPeriods.Marking (DefinitionsIntegral.Index g) A) :
    HodgeConjecture.DegreeTwo.Transport.Constructions.AbelianModel A ≃ₗ[ℂ] DefinitionsIntegral.Tangent g :=
  LinearEquiv.ofFinrankEq _ _ (by rw [native_tangent_finrank A b]; simp [DefinitionsIntegral.Tangent])

lemma native_real_period_map (A : ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety) (b : ArithmeticGeometry.Descent.CMVariety.MarkedAbelianPeriods.IntrinsicPeriods.Marking (DefinitionsIntegral.Index g) A)
    (x : DefinitionsIntegral.Index g → ℝ) :
    ArithmeticGeometry.Descent.CMVariety.MarkedAbelianPeriods.IntrinsicPeriods.periodMap b (fun i => (x i : ℂ)) = (b.ofZLatticeBasis ℝ).equivFun.symm x := by
  rw [ArithmeticGeometry.Descent.CMVariety.MarkedAbelianPeriods.IntrinsicPeriods.periodMap_apply, Module.Basis.equivFun_symm_apply]
  apply Finset.sum_congr rfl
  intro i _
  rw [Module.Basis.ofZLatticeBasis_apply]
  exact IsScalarTower.algebraMap_smul ℂ (x i) (b i : HodgeConjecture.DegreeTwo.Transport.Constructions.AbelianModel A)

lemma native_real_period_bijective (A : ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety) (b : ArithmeticGeometry.Descent.CMVariety.MarkedAbelianPeriods.IntrinsicPeriods.Marking (DefinitionsIntegral.Index g) A) :
    Function.Bijective (fun x : DefinitionsIntegral.Index g → ℝ => ArithmeticGeometry.Descent.CMVariety.MarkedAbelianPeriods.IntrinsicPeriods.periodMap b (fun i => (x i : ℂ))) := by
  have he : (fun x : DefinitionsIntegral.Index g → ℝ => ArithmeticGeometry.Descent.CMVariety.MarkedAbelianPeriods.IntrinsicPeriods.periodMap b (fun i => (x i : ℂ))) =
      (b.ofZLatticeBasis ℝ).equivFun.symm := funext (native_real_period_map A b)
  rw [he]
  exact (b.ofZLatticeBasis ℝ).equivFun.symm.bijective

/-- Natural marking condition on the original polarization's Riemann form. -/
def PreservesPolarizationMatrix (A : ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety)
    (L : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle A.toOver.left) (hL : L.IsAmple)
    (b : ArithmeticGeometry.Descent.CMVariety.MarkedAbelianPeriods.IntrinsicPeriods.Marking (DefinitionsIntegral.Index g) A) (E : DefinitionsIntegral.IntegralMatrix g) : Prop :=
  ∀ i j, (AbelianModuli.ReferenceFamily.Intrinsic.RiemannForm.nativeRiemannForm A L hL (b i : HodgeConjecture.DegreeTwo.Transport.Constructions.AbelianModel A) (b j : HodgeConjecture.DegreeTwo.Transport.Constructions.AbelianModel A)).im = (E i j : ℝ)

lemma native_polarization_marking (A : ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety)
    (L : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle A.toOver.left) (hL : L.IsAmple)
    (b : ArithmeticGeometry.Descent.CMVariety.MarkedAbelianPeriods.IntrinsicPeriods.Marking (DefinitionsIntegral.Index g) A) (E : DefinitionsIntegral.IntegralMatrix g)
    (hb : PreservesPolarizationMatrix A L hL b E)
    (x y : DefinitionsIntegral.Index g → ℝ) :
    (AbelianModuli.ReferenceFamily.Intrinsic.RiemannForm.nativeRiemannForm A L hL
      (ArithmeticGeometry.Descent.CMVariety.MarkedAbelianPeriods.IntrinsicPeriods.periodMap b (fun i => (x i : ℂ)))
      (ArithmeticGeometry.Descent.CMVariety.MarkedAbelianPeriods.IntrinsicPeriods.periodMap b (fun i => (y i : ℂ)))).im =
      (DefinitionsIntegral.pairing E (fun i => (x i : ℂ)) (fun i => (y i : ℂ))).re := by
  let H : HodgeConjecture.DegreeTwo.Transport.Constructions.AbelianModel A →ₗ⋆[ℂ] HodgeConjecture.DegreeTwo.Transport.Constructions.AbelianModel A →ₗ[ℂ] ℂ := AbelianModuli.ReferenceFamily.Intrinsic.RiemannForm.nativeRiemannForm A L hL
  change (H (ArithmeticGeometry.Descent.CMVariety.MarkedAbelianPeriods.IntrinsicPeriods.periodMap b (fun i => (x i : ℂ)))
    (ArithmeticGeometry.Descent.CMVariety.MarkedAbelianPeriods.IntrinsicPeriods.periodMap b (fun i => (y i : ℂ)))).im = _
  have hb' (i j : DefinitionsIntegral.Index g) : (H (b i) (b j)).im = (E i j : ℝ) := hb i j
  have hs (a : ℝ) (u v : HodgeConjecture.DegreeTwo.Transport.Constructions.AbelianModel A) : (H (a • u) v).im = a * (H u v).im := by
    rw [← IsScalarTower.algebraMap_smul ℂ a u, H.map_smulₛₗ, LinearMap.smul_apply]
    simp
  simp only [ArithmeticGeometry.Descent.CMVariety.MarkedAbelianPeriods.IntrinsicPeriods.periodMap_apply, map_sum, LinearMap.sum_apply]
  simp [DefinitionsIntegral.pairing, hs, hb']
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

/-- Construct ThetaConstruction data from the original polarized object and retain its
exact marked period map, actual exponential lattice, and Riemann form. -/
theorem native_polarized_comparison (A : ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety)
    (L : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle A.toOver.left) (hL : L.IsAmple)
    (b : ArithmeticGeometry.Descent.CMVariety.MarkedAbelianPeriods.IntrinsicPeriods.Marking (DefinitionsIntegral.Index g) A) (E : DefinitionsIntegral.IntegralMatrix g)
    (hb : PreservesPolarizationMatrix A L hL b E) :
    ∃ (T : DefinitionsIntegral.MarkedPolarizedTorus g E)
      (e : HodgeConjecture.DegreeTwo.Transport.Constructions.AbelianModel A ≃ₗ[ℂ] DefinitionsIntegral.Tangent g),
      (∀ z, T.periodMap z = e (ArithmeticGeometry.Descent.CMVariety.MarkedAbelianPeriods.IntrinsicPeriods.periodMap b z)) ∧
      (∀ v, v ∈ T.lattice ↔ e.symm v ∈ HodgeConjecture.DegreeTwo.AbelianUniformizationEq.Constructions.AbelianUniformization.periodLattice A) ∧
      (∀ u v, T.riemannForm (e u) (e v) = AbelianModuli.ReferenceFamily.Intrinsic.RiemannForm.nativeRiemannForm A L hL u v) := by
  let e := nativeTangentCoordinates A b
  let π := e.toLinearMap.comp (ArithmeticGeometry.Descent.CMVariety.MarkedAbelianPeriods.IntrinsicPeriods.periodMap b)
  have hreal : Function.Bijective ((π.restrictScalars ℝ).comp DefinitionsIntegral.realInclusion) :=
    e.bijective.comp (native_real_period_bijective A b)
  obtain ⟨Γ, hΓ, hd, hc⟩ := DefinitionsIntegral.marked_lattice π hreal
  let H₀ := AbelianModuli.ReferenceFamily.Intrinsic.RiemannForm.nativeRiemannForm A L hL
  let H : DefinitionsIntegral.Tangent g →ₗ⋆[ℂ] DefinitionsIntegral.Tangent g →ₗ[ℂ] ℂ :=
    (H₀.comp e.symm.toLinearMap).compl₂ e.symm.toLinearMap
  have hH (u v : DefinitionsIntegral.Tangent g) : H u v = H₀ (e.symm u) (e.symm v) := rfl
  have hsym (u v : DefinitionsIntegral.Tangent g) : H v u = star (H u v) :=
    AbelianModuli.ReferenceFamily.Intrinsic.RiemannForm.nativeRiemannForm_symmetry A L hL (e.symm u) (e.symm v)
  have hpos (u : DefinitionsIntegral.Tangent g) (hu : u ≠ 0) : 0 < (H u u).re :=
    AbelianModuli.ReferenceFamily.Intrinsic.RiemannForm.nativeRiemannForm_positive A L hL (e.symm u)
      (fun hz => hu (e.symm.injective (hz.trans e.symm.map_zero.symm)))
  have hmark (x y : DefinitionsIntegral.Index g → ℝ) :
      (H (π (fun i => (x i : ℂ))) (π (fun i => (y i : ℂ)))).im =
      (DefinitionsIntegral.pairing E (fun i => (x i : ℂ)) (fun i => (y i : ℂ))).re := by
    simp only [hH, π, LinearMap.comp_apply, LinearEquiv.coe_coe, e.symm_apply_apply]
    exact native_polarization_marking A L hL b E hb x y
  have hint : ∀ u ∈ Γ, ∀ v ∈ Γ, ∃ n : ℤ, (H u v).im = (n : ℝ) := by
    intro u hu v hv
    obtain ⟨n, rfl⟩ := (hΓ u).mp hu
    obtain ⟨m, rfl⟩ := (hΓ v).mp hv
    refine ⟨∑ i, ∑ j, n i * E i j * m j, ?_⟩
    simpa [DefinitionsIntegral.pairing] using hmark (fun i => (n i : ℝ)) (fun i => (m i : ℝ))
  let : DiscreteTopology Γ := hd
  let : CompactSpace (DefinitionsIntegral.Tangent g ⧸ Γ) := hc
  let T : DefinitionsIntegral.MarkedPolarizedTorus g E := {
    periodMap := π
    real_marking := hreal
    lattice := Γ
    lattice_marking := hΓ
    discrete := hd
    compact := hc
    projective := (Geometry.ComplexTorus.RiemannProjectivity.ProjectivityCriterion.riemann_projectivity_criterion (DefinitionsIntegral.Tangent g) Γ).mpr
      ⟨H, hsym, hpos, hint⟩
    riemannForm := H
    hermitian := hsym
    positive := hpos
    polarization_marking := hmark }
  refine ⟨T, e, fun z => rfl, ?_, ?_⟩
  · intro v
    change v ∈ Γ ↔ e.symm v ∈ HodgeConjecture.DegreeTwo.AbelianUniformizationEq.Constructions.AbelianUniformization.periodLattice A
    rw [hΓ]
    constructor
    · rintro ⟨n, rfl⟩
      simp only [π, LinearMap.comp_apply, LinearEquiv.coe_coe, e.symm_apply_apply]
      exact ArithmeticGeometry.Descent.CMVariety.MarkedAbelianPeriods.IntrinsicPeriods.periodMap_integer_mem b n
    · intro hv
      refine ⟨fun i => b.repr ⟨e.symm v, hv⟩ i, ?_⟩
      change v = e (ArithmeticGeometry.Descent.CMVariety.MarkedAbelianPeriods.IntrinsicPeriods.periodMap b (fun i => (b.repr ⟨e.symm v, hv⟩ i : ℂ)))
      rw [ArithmeticGeometry.Descent.CMVariety.MarkedAbelianPeriods.IntrinsicPeriods.periodMap_repr, e.apply_symm_apply]
  · intro u v
    change H (e u) (e v) = H₀ u v
    rw [hH, e.symm_apply_apply, e.symm_apply_apply]

end

end OAI.AlgebraicGeometry.Picard.ThetaConstruction.IntrinsicPolarization.Geometric

import OAI.Analysis.PDE.Concentration.EnergyCoordinates
import OAI.Analysis.PDE.Concentration.Lattice.Classical
import OAI.Analysis.PDE.Concentration.Cylinder.Monotone

namespace OAI.Analysis.PDE.Concentration

open _root_.MeasureTheory OAI.Analysis.Calculus.Current OAI.Analysis.PDE.Dirichlet OAI.Analysis.PDE.Green
open Laplacian InnerProductSpace Set
open scoped ContDiff Matrix.Norms.Elementwise

/-- One absolute constant works for all dimensions, physical energy data,
and inner radii. The weak differential inequality and nonnegativity are
the interfaces supplied by `EnergyPhysicalPropagation` and
`EnergyPhysicalComparison`, respectively. -/
theorem exists_latticeEnergy_cylinder_constant : ∃ C : ℝ, 0 < C ∧
    ∀ (d : ℕ) (R : OAI.Analysis.Calculus.Current.SpatialSpace d ≃L[ℝ] OAI.Analysis.Calculus.Current.SpatialSpace d) (a : ℝ), 0 < a → 4 * a ≤ 1 →
    ∀ (e : Fin 3 → Quaternion ℝ) (lam : ℝ)
      (A : OAI.Analysis.PDE.Dirichlet.CoordinateSpace (d + 2) 3 → Matrix (Fin (d + 2)) (Fin (d + 2)) (Quaternion ℝ)),
    ContDiff ℝ ∞ A → ∀ B u : OAI.Analysis.PDE.Dirichlet.CoordinateSpace (d + 2) 3 → ℝ,
    ContDiff ℝ ∞ B → ContDiff ℝ ∞ u → ∀ δ : ℝ, 0 ≤ δ →
    (∀ η : OAI.Analysis.PDE.Dirichlet.CoordinateSpace 1 3 → ℝ, ContDiff ℝ ∞ η → HasCompactSupport η →
      tsupport η ⊆ physicalEnergyAnnulus a → (∀ z, 0 ≤ η z) →
      (∫ z, Δ η z * OAI.Analysis.PDE.Green.setFiberCombinedEnergy e lam (physicalLatticeEnergyCell R a) A B u z) ≤
        δ * ∫ z, η z) →
    (∀ z ∈ physicalEnergyAnnulus a,
      0 ≤ OAI.Analysis.PDE.Green.setFiberCombinedEnergy e lam (physicalLatticeEnergyCell R a) A B u z) → ∀ θ : ℝ,
    (∫ t in (1 : ℝ)..2, ∫ φ in (0 : ℝ)..(2 * Real.pi),
      OAI.Analysis.PDE.Green.setFiberCombinedEnergy e lam (physicalLatticeEnergyCell R a) A B u
        (cylinderEnergyEquiv (cylinderPoint t (2 * a) φ))) ≤
      C * (1 + |Real.log (2 * a)|) ^ 3 *
        (OAI.Analysis.PDE.Green.setFiberCombinedEnergy e lam (physicalLatticeEnergyCell R a) A B u
          (cylinderEnergyEquiv (cylinderPoint 0 (4 * a) θ)) + 4 * δ) := by
  obtain ⟨C, hC, hcylinder⟩ := exists_source_cylinder_concentration_constant
  refine ⟨C, hC, ?_⟩
  intro d R a ha ha4 e lam A hA B u hB hu δ hδ hweak hn θ
  let F := OAI.Analysis.PDE.Green.setFiberCombinedEnergy e lam (physicalLatticeEnergyCell R a) A B u
  let G : OAI.Analysis.PDE.Dirichlet.CoordinateSpace 1 3 → ℝ := fun z => F z + (δ / 4) * (16 - ‖OAI.Analysis.PDE.Green.energyComplexTime z‖ ^ 2)
  have hF : ContDiffOn ℝ ∞ F (physicalEnergyAnnulus a) :=
    (contDiffOn_physicalLatticeCombinedEnergy R a ha e lam hA hB hu).mono (fun z hz => hz.1)
  have hQ : ContDiff ℝ ∞ (fun z : OAI.Analysis.PDE.Dirichlet.CoordinateSpace 1 3 =>
      (δ / 4) * (16 - ‖OAI.Analysis.PDE.Green.energyComplexTime z‖ ^ 2)) := by
    simp_rw [energyComplexTime_norm_sq]
    fun_prop
  have hG : ContDiffOn ℝ ∞ G (physicalEnergyAnnulus a) := hF.add hQ.contDiffOn
  have hmem {x : CylinderSpace} (hx : x ∈ cylinderAnnulus a) :
      cylinderEnergyEquiv x ∈ physicalEnergyAnnulus a := by
    change x ∈ cylinderEnergyEquiv ⁻¹' physicalEnergyAnnulus a
    rwa [cylinderEnergyEquiv_preimage_annulus]
  have hGF {x : CylinderSpace} (hx : x ∈ cylinderAnnulus a) :
      F (cylinderEnergyEquiv x) ≤ G (cylinderEnergyEquiv x) := by
    have hz := hmem hx
    have hnorm := norm_nonneg (OAI.Analysis.PDE.Green.energyComplexTime (cylinderEnergyEquiv x))
    have hbound := hz.2
    have hnonneg : 0 ≤ (δ / 4) * (16 - ‖OAI.Analysis.PDE.Green.energyComplexTime (cylinderEnergyEquiv x)‖ ^ 2) :=
      mul_nonneg (by positivity) (by nlinarith)
    dsimp [G]
    linarith
  have hnonneg : ∀ x ∈ cylinderAnnulus a, 0 ≤ (G ∘ cylinderEnergyEquiv) x := by
    intro x hx
    exact (hn _ (hmem hx)).trans (hGF hx)
  have hsuper : ∀ x ∈ cylinderAnnulus a, Δ (G ∘ cylinderEnergyEquiv) x ≤ 0 := by
    intro x hx
    rw [laplacian_comp_cylinderEnergyEquiv]
    exact (corrected_latticeEnergy_superharmonic R a ha e lam hA hB hu hδ hweak hn
      _ (hmem hx)).2
  have hbound := hcylinder a ha ha4 (G ∘ cylinderEnergyEquiv)
    (contDiffOn_comp_cylinderEnergyEquiv hG) hnonneg hsuper θ
  have hKU : cylinderShell 1 2 (2 * a) (2 * a) ⊆ cylinderAnnulus a := by
    intro x hx
    exact ⟨by linarith [hx.2.1], by linarith [hx.2.2]⟩
  have hmono := cylinderTimeTrace_mono_on (isOpen_cylinderAnnulus a)
    (contDiffOn_comp_cylinderEnergyEquiv hF) (contDiffOn_comp_cylinderEnergyEquiv hG)
    (by positivity : 0 ≤ 2 * a) hKU (fun x hx => hGF (hKU hx))
  have hinitial : G (cylinderEnergyEquiv (cylinderPoint 0 (4 * a) θ)) ≤
      F (cylinderEnergyEquiv (cylinderPoint 0 (4 * a) θ)) + 4 * δ := by
    have hq := mul_nonneg (div_nonneg hδ (by norm_num : (0 : ℝ) ≤ 4))
      (sq_nonneg ‖OAI.Analysis.PDE.Green.energyComplexTime (cylinderEnergyEquiv (cylinderPoint 0 (4 * a) θ))‖)
    dsimp [G]
    nlinarith
  have hlast := mul_le_mul_of_nonneg_left hinitial
    (show 0 ≤ C * (1 + |Real.log (2 * a)|) ^ 3 by positivity)
  simp only [cylinderAngularAverage, Function.comp_apply] at hmono hbound
  exact hmono.trans (hbound.trans hlast)

end OAI.Analysis.PDE.Concentration

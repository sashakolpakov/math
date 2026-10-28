import OAI.AlgebraicGeometry.HilbertScheme.Presentations.PivotCochainLifts
import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Cech.ContractionLift

/-! # Variable Torsion -/

namespace OAI.AlgebraicGeometry.HilbertScheme.Presentations.Cech.VariableTorsion.ProjectiveCech

noncomputable section

/-! Every actual projective Čech cohomology class is killed by a power of each variable. -/

open _root_.MvPolynomial

universe u v w

variable {σ : Type u} [Fintype σ] [LinearOrder σ]
variable (R : Type v) [CommRing R]
variable (M : Type w) [AddCommGroup M] [Module R M] [Module (MvPolynomial σ R) M]
  [IsScalarTower R (MvPolynomial σ R) M]

theorem moduleCech_variable_power_boundary (j : σ) (q : ℕ)
    (f : ModuleCech.Card.ProjectiveCech.ModuleCechFamily (σ := σ) R M) (hf : ModuleCech.Card.ProjectiveCech.ModuleCechCardSupported R M q f)
    (hcycle : ModuleCech.Card.ProjectiveCech.moduleCechDifferential R M f = 0) :
    ∃ (k : ℕ) (g : ModuleCech.Card.ProjectiveCech.ModuleCechFamily (σ := σ) R M),
      ModuleCech.Card.ProjectiveCech.ModuleCechCardSupported R M (q - 1) g ∧
      ModuleCech.Card.ProjectiveCech.moduleCechDifferential R M g = X (R := R) j ^ k • f := by
  classical
  obtain ⟨k, g, hgc, hgz, hg⟩ := PivotCochainLifts.ProjectiveCech.moduleCech_pivot_power_lift R M j f q hf
  have hfc : ModuleCech.Card.ProjectiveCech.moduleCechDifferential R M (X (R := R) j ^ k • f) = 0 := by
    rw [PolynomialScalars.ProjectiveCech.moduleCechDifferential_polynomial_smul, hcycle, smul_zero]
  have he (s : Finset σ) : ∃ l : ℕ,
      X (R := R) j ^ l • (ModuleCech.Card.ProjectiveCech.moduleCechDifferential R M g s - X (R := R) j ^ k • f s) = 0 := by
    apply PivotChartTorsion.ProjectiveCech.modulePivotChart_kernel_power R M j s
    rw [map_sub, ContractionLift.ProjectiveCech.moduleCech_contraction_lift_restrict R M j (X (R := R) j ^ k • f) g hgz hg hfc s,
      Pi.smul_apply, sub_self]
  choose l hl using he
  let L : ℕ := ∑ s : Finset σ, l s
  have hL (s : Finset σ) : l s ≤ L :=
    Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ s)
  have herr (s : Finset σ) :
      X (R := R) j ^ L • (ModuleCech.Card.ProjectiveCech.moduleCechDifferential R M g s - X (R := R) j ^ k • f s) = 0 := by
    calc
      _ = X (R := R) j ^ (L - l s) •
          (X (R := R) j ^ l s • (ModuleCech.Card.ProjectiveCech.moduleCechDifferential R M g s - X (R := R) j ^ k • f s)) := by
        rw [smul_smul, ← pow_add, Nat.sub_add_cancel (hL s)]
      _ = 0 := by rw [hl s, smul_zero]
  refine ⟨L + k, X (R := R) j ^ L • g, ?_, ?_⟩
  · intro s hs
    change X (R := R) j ^ L • g s = 0
    rw [hgc s hs, smul_zero]
  · rw [PolynomialScalars.ProjectiveCech.moduleCechDifferential_polynomial_smul]
    funext s
    have h := sub_eq_zero.mp (by simpa only [smul_sub] using herr s)
    change X (R := R) j ^ L • ModuleCech.Card.ProjectiveCech.moduleCechDifferential R M g s = X (R := R) j ^ (L + k) • f s
    rw [h, smul_smul, ← pow_add]

end

end OAI.AlgebraicGeometry.HilbertScheme.Presentations.Cech.VariableTorsion.ProjectiveCech

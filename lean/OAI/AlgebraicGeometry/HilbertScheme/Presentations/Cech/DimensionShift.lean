import OAI.AlgebraicGeometry.HilbertScheme.Presentations.ModuleCech.ExactSequences
import OAI.AlgebraicGeometry.HilbertScheme.Presentations.FreeModuleCechExactness

/-! # Dimension Shift -/

namespace OAI.AlgebraicGeometry.HilbertScheme.Presentations.Cech.DimensionShift.ProjectiveCech

noncomputable section

/-! The exact-sequence diagram chase used in eventual Čech vanishing. -/

open _root_.MvPolynomial DirectSum

universe u v w t

variable {σ : Type u} [LinearOrder σ]
variable (R : Type v) [CommRing R]
variable (M : Type w) [AddCommGroup M] [Module R M] [Module (MvPolynomial σ R) M]
  [IsScalarTower R (MvPolynomial σ R) M]
variable (ℳ : ℤ → Submodule R M)

/-- In degree zero the primitive has degree zero too; cardinal support
then forces the cocycle to vanish. In positive degrees this is ordinary exactness. -/
def ModuleCechExactAt (d : ℤ) (q : ℕ) : Prop :=
  ∀ f : ModuleCech.Card.ProjectiveCech.ModuleCechFamily (σ := σ) R M,
    ModuleCech.Card.ProjectiveCech.ModuleCechHomogeneous R M ℳ d f → ModuleCech.Card.ProjectiveCech.ModuleCechCardSupported R M q f →
    ModuleCech.Card.ProjectiveCech.moduleCechDifferential R M f = 0 →
    ∃ g : ModuleCech.Card.ProjectiveCech.ModuleCechFamily (σ := σ) R M,
      ModuleCech.Card.ProjectiveCech.ModuleCechHomogeneous R M ℳ d g ∧ ModuleCech.Card.ProjectiveCech.ModuleCechCardSupported R M (q - 1) g ∧
      ModuleCech.Card.ProjectiveCech.moduleCechDifferential R M g = f

theorem moduleCechExactAt_of_bounded [Fintype σ] (d : ℤ) (q : ℕ) (hq : Fintype.card σ < q) :
    ModuleCechExactAt (σ := σ) R M ℳ d q := by
  intro f _ hcard _
  have hf := ModuleCech.Card.ProjectiveCech.moduleCech_bounded R M q hq f hcard
  refine ⟨0, fun s => Submodule.zero_mem _, fun _ _ => rfl, ?_⟩
  rw [map_zero, hf]

variable {N : Type t} [AddCommGroup N] [Module R N] [Module (MvPolynomial σ R) N]
  [IsScalarTower R (MvPolynomial σ R) N]
variable (𝒩 : ℤ → Submodule R N)
variable {P : Type*} [AddCommGroup P] [Module R P] [Module (MvPolynomial σ R) P]
  [IsScalarTower R (MvPolynomial σ R) P]
variable (ℙ : ℤ → Submodule R P)
variable [Decomposition ℳ] [Decomposition 𝒩] [Decomposition ℙ]
variable [SetLike.GradedSMul (WeightedFreeModules.GradedModules.polynomialIntegerGrading (σ := σ) R) ℳ]
  [SetLike.GradedSMul (WeightedFreeModules.GradedModules.polynomialIntegerGrading (σ := σ) R) 𝒩]
  [SetLike.GradedSMul (WeightedFreeModules.GradedModules.polynomialIntegerGrading (σ := σ) R) ℙ]

theorem moduleCech_dimension_shift (i : M →ₗ[MvPolynomial σ R] N) (p : N →ₗ[MvPolynomial σ R] P)
    (hi : ∀ d m, m ∈ ℳ d → i m ∈ 𝒩 d) (hp : ∀ d n, n ∈ 𝒩 d → p n ∈ ℙ d)
    (hinj : Function.Injective i) (hsurj : Function.Surjective p) (hex : Function.Exact i p)
    (d : ℤ) (q : ℕ) (hM : ModuleCechExactAt (σ := σ) R M ℳ d (q + 1))
    (hN : ModuleCechExactAt (σ := σ) R N 𝒩 d q) : ModuleCechExactAt (σ := σ) R P ℙ d q := by
  intro f hf hcard hcycle
  obtain ⟨y, hy, hycard, hyp⟩ := ModuleCech.ExactSequences.ProjectiveCech.moduleCechMap_lift R 𝒩 ℙ p hp hsurj d q f hf hcard
  have hdy : ModuleCech.Maps.ProjectiveCech.moduleCechMap R p (ModuleCech.Card.ProjectiveCech.moduleCechDifferential R N y) = 0 := by
    rw [ModuleCech.Maps.ProjectiveCech.moduleCechMap_differential, hyp, hcycle]
  obtain ⟨z, hz, hzcard, hzi⟩ := ModuleCech.ExactSequences.ProjectiveCech.moduleCechMap_kernel_lift R ℳ 𝒩 ℙ i p hi hp hex d (q + 1)
    (ModuleCech.Card.ProjectiveCech.moduleCechDifferential R N y) (ModuleCech.Card.ProjectiveCech.moduleCechDifferential_homogeneous R N 𝒩 d y hy)
    (ModuleCech.Card.ProjectiveCech.moduleCechDifferential_card R N q y hycard) hdy
  have hdz : ModuleCech.Card.ProjectiveCech.moduleCechDifferential R M z = 0 := by
    apply ModuleCech.Maps.ProjectiveCech.moduleCechMap_injective R i hinj
    rw [map_zero, ModuleCech.Maps.ProjectiveCech.moduleCechMap_differential, hzi, ModuleCech.Square.ProjectiveCech.moduleCechDifferential_square]
  obtain ⟨u, hu, hucard, hdu⟩ := hM z hz hzcard hdz
  simp only [Nat.add_sub_cancel] at hucard
  let y' := y - ModuleCech.Maps.ProjectiveCech.moduleCechMap R i u
  have hy' : ModuleCech.Card.ProjectiveCech.ModuleCechHomogeneous R N 𝒩 d y' := by
    intro s
    exact Submodule.sub_mem _ (hy s) (ModuleCech.Maps.ProjectiveCech.moduleCechMap_homogeneous R ℳ 𝒩 i hi d u hu s)
  have hy'card : ModuleCech.Card.ProjectiveCech.ModuleCechCardSupported R N q y' := by
    intro s hs
    change y s - ModuleCech.Maps.ProjectiveCech.moduleCechMap R i u s = 0
    rw [hycard s hs, ModuleCech.Maps.ProjectiveCech.moduleCechMap_card R i q u hucard s hs, sub_self]
  have hdy' : ModuleCech.Card.ProjectiveCech.moduleCechDifferential R N y' = 0 := by
    change ModuleCech.Card.ProjectiveCech.moduleCechDifferential R N (y - ModuleCech.Maps.ProjectiveCech.moduleCechMap R i u) = 0
    rw [map_sub, ← ModuleCech.Maps.ProjectiveCech.moduleCechMap_differential, hdu, hzi, sub_self]
  obtain ⟨v, hv, hvcard, hdv⟩ := hN y' hy' hy'card hdy'
  refine ⟨ModuleCech.Maps.ProjectiveCech.moduleCechMap R p v, ModuleCech.Maps.ProjectiveCech.moduleCechMap_homogeneous R 𝒩 ℙ p hp d v hv,
    ModuleCech.Maps.ProjectiveCech.moduleCechMap_card R p (q - 1) v hvcard, ?_⟩
  rw [← ModuleCech.Maps.ProjectiveCech.moduleCechMap_differential, hdv]
  change ModuleCech.Maps.ProjectiveCech.moduleCechMap R p (y - ModuleCech.Maps.ProjectiveCech.moduleCechMap R i u) = f
  rw [map_sub, hyp, (ModuleCech.Maps.ProjectiveCech.moduleCechMap_exact R i p hex (ModuleCech.Maps.ProjectiveCech.moduleCechMap R i u)).mpr ⟨u, rfl⟩, sub_zero]

end

end OAI.AlgebraicGeometry.HilbertScheme.Presentations.Cech.DimensionShift.ProjectiveCech

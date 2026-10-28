import OAI.AlgebraicGeometry.HilbertScheme.Presentations.AddedKernelExactness

/-! # Cover Expansion -/

namespace OAI.AlgebraicGeometry.HilbertScheme.Presentations.Linear.CoverExpansion.ProjectiveCech

noncomputable section

/-! Adjoining a homogeneous linear form to the coordinate cover preserves and reflects augmented Čech exactness. -/

open _root_.MvPolynomial DirectSum

universe u v w

variable {σ : Type u} [Fintype σ] [LinearOrder σ]
variable (R : Type v) [CommRing R]
variable [Algebra (MvPolynomial (WithBot σ) R) (MvPolynomial σ R)]
  [IsScalarTower R (MvPolynomial (WithBot σ) R) (MvPolynomial σ R)]
variable (he : ∀ i : σ, algebraMap (MvPolynomial (WithBot σ) R) (MvPolynomial σ R) (X (i : WithBot σ)) = X i)
variable (M : Type w) [AddCommGroup M] [Module R M]
  [Module (MvPolynomial (WithBot σ) R) M] [Module (MvPolynomial σ R) M]
  [IsScalarTower R (MvPolynomial (WithBot σ) R) M] [IsScalarTower R (MvPolynomial σ R) M]
  [IsScalarTower (MvPolynomial (WithBot σ) R) (MvPolynomial σ R) M]
variable (l : MvPolynomial σ R)
variable (hl : algebraMap (MvPolynomial (WithBot σ) R) (MvPolynomial σ R) (X ⊥) = l)
variable (ℳ : ℤ → Submodule R M) [Decomposition ℳ]
  [SetLike.GradedSMul (WeightedFreeModules.GradedModules.polynomialIntegerGrading (σ := σ) R) ℳ]
  [SetLike.GradedSMul (WeightedFreeModules.GradedModules.polynomialIntegerGrading (σ := WithBot σ) R) ℳ]

include he hl in
theorem linearCoverExpansion_moduleCechExactAt_iff (hlhom : l.IsHomogeneous 1) (d : ℤ) (q : ℕ) :
    Cech.DimensionShift.ProjectiveCech.ModuleCechExactAt (σ := WithBot σ) R M ℳ d q ↔ Cech.DimensionShift.ProjectiveCech.ModuleCechExactAt (σ := σ) R M ℳ d q := by
  let p := ModuleCech.HomogeneousLift.ProjectiveCech.retainedModuleCechMap R Function.Embedding.coeWithBot he M
  let dB := ModuleCech.Card.ProjectiveCech.moduleCechDifferential (σ := WithBot σ) R M
  let dS := ModuleCech.Card.ProjectiveCech.moduleCechDifferential (σ := σ) R M
  let e : σ ↪o WithBot σ :=
    { toEmbedding := Function.Embedding.coeWithBot, map_rel_iff' := WithBot.coe_le_coe }
  have he' : ∀ i : σ, algebraMap (MvPolynomial (WithBot σ) R) (MvPolynomial σ R) (X (e i)) = X i := he
  have hcomm (x : ModuleCech.Card.ProjectiveCech.ModuleCechFamily (σ := WithBot σ) R M) : p (dB x) = dS (p x) :=
    Cech.CechDifferential.ProjectiveCech.retainedModuleCechMap_differential R e he' M x
  constructor
  · intro hBig y hy hyc hyd
    obtain ⟨x, hx, hxc, hpx⟩ := ModuleCech.HomogeneousLift.ProjectiveCech.retainedModuleCechMap_homogeneous_lift R Function.Embedding.coeWithBot he M ℳ d q y hy hyc
    change p x = y at hpx
    have hpdx : p (dB x) = 0 := by rw [hcomm, hpx]; exact hyd
    obtain ⟨z, hz, hzc, hpz, hdz⟩ := AddedKernelExactness.ProjectiveCech.addedModuleCechKernel_exact R he M l hl ℳ hlhom d (q + 1)
      (dB x) (ModuleCech.Card.ProjectiveCech.moduleCechDifferential_homogeneous R M ℳ d x hx)
      (ModuleCech.Card.ProjectiveCech.moduleCechDifferential_card R M q x hxc) hpdx (ModuleCech.Square.ProjectiveCech.moduleCechDifferential_square R M x)
    have hdiff : ModuleCech.Card.ProjectiveCech.ModuleCechHomogeneous R M ℳ d (x - z) := fun s => Submodule.sub_mem _ (hx s) (hz s)
    have hdiffc : ModuleCech.Card.ProjectiveCech.ModuleCechCardSupported R M q (x - z) := by
      intro s hs
      change x s - z s = 0
      rw [hxc s hs, hzc s (by simpa only [Nat.add_sub_cancel] using hs), sub_self]
    have hcycle : dB (x - z) = 0 := by rw [map_sub, hdz, sub_self]
    obtain ⟨a, ha, hac, had⟩ := hBig (x - z) hdiff hdiffc hcycle
    refine ⟨p a, ModuleCech.HomogeneousLift.ProjectiveCech.retainedModuleCechMap_homogeneous R Function.Embedding.coeWithBot he M ℳ d a ha,
      ModuleCech.HomogeneousLift.ProjectiveCech.retainedModuleCechMap_card R Function.Embedding.coeWithBot he M (q - 1) a hac, ?_⟩
    change dS (p a) = y
    rw [← hcomm, had, map_sub, hpx, hpz, sub_zero]
  · intro hSmall x hx hxc hxd
    have hpxh := ModuleCech.HomogeneousLift.ProjectiveCech.retainedModuleCechMap_homogeneous R Function.Embedding.coeWithBot he M ℳ d x hx
    have hpxc := ModuleCech.HomogeneousLift.ProjectiveCech.retainedModuleCechMap_card R Function.Embedding.coeWithBot he M q x hxc
    have hpxd : dS (p x) = 0 := by rw [← hcomm, hxd, map_zero]
    cases q with
    | zero =>
      have hpxzero := Cech.ExactLeft.ProjectiveCech.moduleCechExactAt_zero_vanish R M ℳ d hSmall (p x) hpxh hpxc hpxd
      obtain ⟨g, hg, hgc, _, hgd⟩ := AddedKernelExactness.ProjectiveCech.addedModuleCechKernel_exact R he M l hl ℳ hlhom d 0 x hx hxc hpxzero hxd
      exact ⟨g, hg, hgc, hgd⟩
    | succ q =>
      obtain ⟨y, hy, hyc, hyd⟩ := hSmall (p x) hpxh hpxc hpxd
      obtain ⟨z, hz, hzc, hpz⟩ := ModuleCech.HomogeneousLift.ProjectiveCech.retainedModuleCechMap_homogeneous_lift R Function.Embedding.coeWithBot he M ℳ d q
        y hy (by simpa only [Nat.succ_sub_one] using hyc)
      change p z = y at hpz
      have hrh : ModuleCech.Card.ProjectiveCech.ModuleCechHomogeneous R M ℳ d (x - dB z) :=
        fun s => Submodule.sub_mem _ (hx s) (ModuleCech.Card.ProjectiveCech.moduleCechDifferential_homogeneous R M ℳ d z hz s)
      have hrc : ModuleCech.Card.ProjectiveCech.ModuleCechCardSupported R M (q + 1) (x - dB z) := by
        intro s hs
        change x s - dB z s = 0
        rw [hxc s hs, ModuleCech.Card.ProjectiveCech.moduleCechDifferential_card R M q z hzc s hs, sub_self]
      have hrp : p (x - dB z) = 0 := by rw [map_sub, hcomm, hpz, hyd, sub_self]
      have hrd : dB (x - dB z) = 0 := by rw [map_sub, hxd, ModuleCech.Square.ProjectiveCech.moduleCechDifferential_square, sub_self]
      obtain ⟨a, ha, hac, _, had⟩ := AddedKernelExactness.ProjectiveCech.addedModuleCechKernel_exact R he M l hl ℳ hlhom d (q + 1)
        (x - dB z) hrh hrc hrp hrd
      refine ⟨z + a, fun s => Submodule.add_mem _ (hz s) (ha s), ?_, ?_⟩
      · intro s hs
        change z s + a s = 0
        rw [hzc s (by simpa only [Nat.succ_sub_one] using hs), hac s hs, add_zero]
      · change dB (z + a) = x
        rw [map_add, had]
        abel

end

end OAI.AlgebraicGeometry.HilbertScheme.Presentations.Linear.CoverExpansion.ProjectiveCech

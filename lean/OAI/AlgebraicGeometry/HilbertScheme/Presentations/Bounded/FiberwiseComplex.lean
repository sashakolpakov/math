import OAI.AlgebraicGeometry.HilbertScheme.Presentations.FiberwiseExactness

/-! # Fiberwise Complex -/

namespace OAI.AlgebraicGeometry.HilbertScheme.Presentations.Bounded.FiberwiseComplex

noncomputable section

/-! A bounded complex of flat modules with finite homology is exact where all its residue-field fibers are exact; its kernels and images are flat. -/

universe u v

variable (R : Type u) [CommRing R]

theorem bounded_fiberwise_exact_flat (n : ℕ) :
    ∀ (V : ℕ → Type v) [∀ q, AddCommGroup (V q)] [∀ q, Module R (V q)]
      (d : ∀ q, V q →ₗ[R] V (q + 1)) (hsquare : ∀ q x, d (q + 1) (d q x) = 0),
      d n = 0 →
      (∀ q, q ≤ n → Module.Flat R (V q)) →
      (∀ q, q < n → Module.Finite R ((d (q + 1)).ker ⧸
        (FiberwiseExactness.linearMapToKernel R (d q) (d (q + 1)) (hsquare q)).range)) →
      (∀ q, q < n → ∀ p : PrimeSpectrum R,
        Function.Exact ((d q).lTensor p.asIdeal.ResidueField) ((d (q + 1)).lTensor p.asIdeal.ResidueField)) →
      Module.Flat R (d 0).ker ∧ Module.Flat R (d 0).range ∧
        ∀ q, q < n → Function.Exact (d q) (d (q + 1)) := by
  induction n with
  | zero =>
    intro V _ _ d _ hd hflat _ _
    let : Module.Flat R (V 0) := hflat 0 le_rfl
    refine ⟨?_, ?_, fun q hq => (Nat.not_lt_zero q hq).elim⟩
    · rw [hd, LinearMap.ker_zero]
      exact Module.Flat.of_linearEquiv Submodule.topEquiv
    · rw [hd, LinearMap.range_zero]
      infer_instance
  | succ n ih =>
    intro V _ _ d hsquare hd hflat hfinite hfiber
    obtain ⟨hker, hrange, hex⟩ := ih (fun q => V (q + 1)) (fun q => d (q + 1))
      (fun q => hsquare (q + 1)) hd
      (fun q hq => hflat (q + 1) (by omega))
      (fun q hq => hfinite (q + 1) (by omega))
      (fun q hq => hfiber (q + 1) (by omega))
    let : Module.Flat R (d 1).ker := hker
    let : Module.Flat R (d 1).range := hrange
    let : Module.Finite R ((d 1).ker ⧸ (FiberwiseExactness.linearMapToKernel R (d 0) (d 1) (hsquare 0)).range) :=
      hfinite 0 (Nat.zero_lt_succ n)
    have hhead := FiberwiseExactness.exact_of_residueFields_of_flat_range R (d 0) (d 1) (hsquare 0)
      (hfiber 0 (Nat.zero_lt_succ n))
    have heq : (d 0).range = (d 1).ker := hhead.linearMap_ker_eq.symm
    let : Module.Flat R (d 0).range := Module.Flat.of_linearEquiv (LinearEquiv.ofEq _ _ heq)
    let : Module.Flat R (V 0) := hflat 0 (Nat.zero_le _)
    refine ⟨FiberwiseExactness.kernel_flat_of_flat_range R (d 0), inferInstance, ?_⟩
    intro q hq
    cases q with
    | zero => exact hhead
    | succ q => exact hex q (by omega)

end

end OAI.AlgebraicGeometry.HilbertScheme.Presentations.Bounded.FiberwiseComplex

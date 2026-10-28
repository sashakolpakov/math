import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Flat.ExactKernels

/-! # Bounded Complex -/

namespace OAI.AlgebraicGeometry.HilbertScheme.Presentations.Flat.BoundedComplex

/-! Flatness at the left end of a bounded exact complex of flat modules. -/

universe u v

variable (R : Type u) [CommRing R]

theorem flat_kernel_of_bounded_exact (n : ℕ) :
    ∀ (V : ℕ → Type v) [∀ q, AddCommGroup (V q)] [∀ q, Module R (V q)]
      (d : ∀ q, V q →ₗ[R] V (q + 1)),
      (∀ q, Function.Exact (d q) (d (q + 1))) → d n = 0 →
      (∀ q, q ≤ n → Module.Flat R (V q)) → Module.Flat R (d 0).ker := by
  induction n with
  | zero =>
    intro V _ _ d _ hd hflat
    let : Module.Flat R (V 0) := hflat 0 le_rfl
    rw [LinearMap.ker_eq_top.mpr hd]
    exact Module.Flat.of_linearEquiv Submodule.topEquiv
  | succ n ih =>
    intro V _ _ d hex hd hflat
    let : Module.Flat R (V 0) := hflat 0 (Nat.zero_le _)
    let : Module.Flat R (d 1).ker :=
      ih (fun q => V (q + 1)) (fun q => d (q + 1)) (fun q => hex (q + 1)) hd
        (fun q hq => hflat (q + 1) (Nat.succ_le_succ hq))
    have hrange : (d 0).range = (d 1).ker := (hex 0).linearMap_ker_eq.symm
    let : Module.Flat R (d 0).range :=
      Module.Flat.of_linearEquiv (LinearEquiv.ofEq _ _ hrange)
    let : Module.Flat R (d 0).rangeRestrict.ker :=
      ExactKernels.kernel_flat_of_surjective (d 0).rangeRestrict (d 0).surjective_rangeRestrict
    exact Module.Flat.of_linearEquiv (LinearEquiv.ofEq _ _ (LinearMap.ker_rangeRestrict (d 0)).symm)

theorem flat_augmentation_of_bounded_exact (n : ℕ)
    (V : ℕ → Type v) [∀ q, AddCommGroup (V q)] [∀ q, Module R (V q)]
    (d : ∀ q, V q →ₗ[R] V (q + 1))
    (hex : ∀ q, Function.Exact (d q) (d (q + 1))) (hd : d (n + 1) = 0)
    (hinj : Function.Injective (d 0)) (hflat : ∀ q, 1 ≤ q → q ≤ n + 1 → Module.Flat R (V q)) :
    Module.Flat R (V 0) := by
  let : Module.Flat R (d 1).ker :=
    flat_kernel_of_bounded_exact R n (fun q => V (q + 1)) (fun q => d (q + 1))
      (fun q => hex (q + 1)) hd (fun q hq => hflat (q + 1) (Nat.succ_pos q) (Nat.succ_le_succ hq))
  have hrange : (d 0).range = (d 1).ker := (hex 0).linearMap_ker_eq.symm
  let : Module.Flat R (d 0).range := Module.Flat.of_linearEquiv (LinearEquiv.ofEq _ _ hrange)
  exact Module.Flat.of_linearEquiv (LinearEquiv.ofInjective (d 0) hinj)

end OAI.AlgebraicGeometry.HilbertScheme.Presentations.Flat.BoundedComplex

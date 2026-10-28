import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Flat.BoundedComplex

/-! # Tensor Bounded Complex -/

namespace OAI.AlgebraicGeometry.HilbertScheme.Presentations.TensorBoundedComplex

/-! The augmentation of a bounded exact complex of flat positive terms remains injective after tensoring. -/

universe u v w

variable (R : Type u) [CommRing R]

theorem flat_range_of_bounded_exact (n : ℕ)
    (V : ℕ → Type v) [∀ q, AddCommGroup (V q)] [∀ q, Module R (V q)]
    (d : ∀ q, V q →ₗ[R] V (q + 1))
    (hex : ∀ q, Function.Exact (d q) (d (q + 1))) (hd : d (n + 2) = 0)
    (hflat : ∀ q, 2 ≤ q → q ≤ n + 2 → Module.Flat R (V q)) :
    Module.Flat R (d 1).range := by
  let : Module.Flat R (d 2).ker :=
    Presentations.Flat.BoundedComplex.flat_kernel_of_bounded_exact R n (fun q => V (q + 2)) (fun q => d (q + 2))
      (fun q => hex (q + 2)) hd (fun q hq => hflat (q + 2) (by omega) (by omega))
  exact Module.Flat.of_linearEquiv (LinearEquiv.ofEq _ _ (hex 1).linearMap_ker_eq.symm)

theorem lTensor_augmentation_injective_of_bounded_exact (n : ℕ)
    (V : ℕ → Type v) [∀ q, AddCommGroup (V q)] [∀ q, Module R (V q)]
    (d : ∀ q, V q →ₗ[R] V (q + 1))
    (hex : ∀ q, Function.Exact (d q) (d (q + 1))) (hd : d (n + 2) = 0)
    (hinj : Function.Injective (d 0))
    (hflat : ∀ q, 2 ≤ q → q ≤ n + 2 → Module.Flat R (V q))
    (S : Type w) [AddCommGroup S] [Module R S] :
    Function.Injective ((d 0).lTensor S) := by
  let : Module.Flat R (d 1).range := flat_range_of_bounded_exact R n V d hex hd hflat
  apply LinearMap.lTensor_injective_of_exact_of_flat (d 1).rangeRestrict
    (d 1).surjective_rangeRestrict (d 0) hinj _ S
  intro x
  constructor
  · intro hx
    exact (hex 0 x).mp (congrArg Subtype.val hx)
  · intro hx
    exact Subtype.ext ((hex 0 x).mpr hx)

end OAI.AlgebraicGeometry.HilbertScheme.Presentations.TensorBoundedComplex

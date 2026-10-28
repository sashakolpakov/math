import OAI.NumberTheory.PadicHodge.GeometricComparison.Finite.PowerTorsion
import Mathlib.RingTheory.AdicCompletion.Basic

/-! # Adic Cohomology -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.AdicCohomology.AdicCohomologyLimit

noncomputable section

/-! Compatible cohomology classes are completed integral classes when the adjacent torsion module is Noetherian. -/

variable {R M N : Type*} [CommRing R] [AddCommGroup M] [Module R M]
  [AddCommGroup N] [Module R N] [IsNoetherian R N]
  (I : Ideal R) (r : R) (B : ℕ → Type*)
  [∀ n, AddCommGroup (B n)] [∀ n, Module R (B n)]
  (t : ∀ n m : ℕ, n ≤ m → B m →ₗ[R] B n)
  (inc : ∀ n, (M ⧸ (I ^ n • ⊤ : Submodule R M)) →ₗ[R] B n)
  (δ : ∀ n, B n →ₗ[R] N)

def compatible : Submodule R (∀ n, B n) where
  carrier := {x | ∀ n m (h : n ≤ m), t n m h (x m) = x n}
  zero_mem' := by intro n m h; exact map_zero _
  add_mem' := by
    intro x y hx hy n m h
    exact (map_add _ _ _).trans (congrArg₂ (· + ·) (hx n m h) (hy n m h))
  smul_mem' := by
    intro a x hx n m h
    exact (map_smul _ _ _).trans (congrArg (a • ·) (hx n m h))

variable (hinc : ∀ n, Function.Injective (inc n))
  (hker : ∀ n, (δ n).ker = (inc n).range)
  (hnat : ∀ n m (h : n ≤ m) x,
    t n m h (inc m x) = inc n (AdicCompletion.transitionMap I M h x))
  (hδ : ∀ n x, r • δ (n + 1) x = δ n (t n (n + 1) (Nat.le_succ n) x))
  (htorsion : ∀ n x, ∃ a : ℕ, r ^ a • δ n x = 0)

include hker hδ htorsion in
theorem compatible_in_range (x : compatible B t) (n : ℕ) : x.val n ∈ (inc n).range := by
  have hz : ∀ n, δ n (x.val n) = 0 :=
    Finite.PowerTorsion.FinitePowerTorsion.compatible_zero r (fun n => δ n (x.val n))
      (fun n => htorsion n (x.val n)) (fun n =>
        (hδ n (x.val (n + 1))).trans (congrArg (δ n) (x.property n (n + 1) (Nat.le_succ n))))
  rw [← hker n]
  exact hz n

def comparison : AdicCompletion I M →ₗ[R] compatible B t where
  toFun x := ⟨fun n => inc n (x.val n), by
    intro n m h
    rw [hnat]
    exact congrArg (inc n) (x.property h)⟩
  map_add' x y := by
    apply Subtype.ext
    funext n
    exact (inc n).map_add _ _
  map_smul' a x := by
    apply Subtype.ext
    funext n
    exact (inc n).map_smul _ _

include hinc in
theorem comparison_injective : Function.Injective (comparison I B t inc hnat) := by
  intro x y h
  apply Subtype.ext
  funext n
  apply hinc n
  exact congrArg (fun z : compatible B t => z.val n) h

include hinc hker hδ htorsion in
theorem comparison_surjective : Function.Surjective (comparison I B t inc hnat) := by
  intro x
  choose y hy using (compatible_in_range I r B t inc δ hker hδ htorsion x)
  let z : AdicCompletion I M := ⟨y, by
    intro n m h
    apply hinc n
    rw [← hnat, hy m, x.property n m h, hy n]⟩
  exact ⟨z, Subtype.ext (funext hy)⟩

def equiv : AdicCompletion I M ≃ₗ[R] compatible B t :=
  LinearEquiv.ofBijective (comparison I B t inc hnat)
    ⟨comparison_injective I B t inc hinc hnat,
      comparison_surjective I r B t inc δ hinc hker hnat hδ htorsion⟩

theorem equiv_eval (x : AdicCompletion I M) (n : ℕ) :
    (equiv I r B t inc δ hinc hker hnat hδ htorsion x).val n = inc n (x.val n) := rfl

end

end OAI.NumberTheory.PadicHodge.GeometricComparison.AdicCohomology.AdicCohomologyLimit

import Mathlib.LinearAlgebra.BilinearMap
import Mathlib.Algebra.Module.Pi

/-! # Compatible Bilinear Product -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.CompatibleBilinearProduct

noncomputable section

/-! A pointwise bilinear operation restricts to submodules of compatible
families whenever its actual coordinates satisfy the compatibility relation. -/

universe u v

variable (R : Type u) [CommRing R] (V : ℕ → ℕ → Type v)
  [∀ n i, AddCommGroup (V n i)] [∀ n i, Module R (V n i)]
  (C : ∀ i, Submodule R (∀ n, V n i))
  (b : ∀ n i j, V n i →ₗ[R] V n j →ₗ[R] V n (i + j))
  (hb : ∀ i j (x : C i) (y : C j), (fun n => b n i j (x.val n) (y.val n)) ∈ C (i + j))

def cup (i j : ℕ) : C i →ₗ[R] C j →ₗ[R] C (i + j) :=
  LinearMap.mk₂ R (fun (x : C i) (y : C j) =>
    (⟨fun n => b n i j (x.val n) (y.val n), hb i j x y⟩ : C (i + j)))
    (fun x z y => Subtype.ext (funext (fun n => LinearMap.congr_fun ((b n i j).map_add (x.val n) (z.val n)) (y.val n))))
    (fun r x y => Subtype.ext (funext (fun n => LinearMap.congr_fun ((b n i j).map_smul r (x.val n)) (y.val n))))
    (fun x y z => Subtype.ext (funext (fun n => (b n i j (x.val n)).map_add (y.val n) (z.val n))))
    (fun r x y => Subtype.ext (funext (fun n => (b n i j (x.val n)).map_smul r (y.val n))))

theorem coordinate (i j n : ℕ) (x : C i) (y : C j) :
    (cup R V C b hb i j x y).val n = b n i j (x.val n) (y.val n) := rfl

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.CompatibleBilinearProduct

import OAI.AlgebraicGeometry.CycleClass.Thom.TorAlgebra.ExactSequence
import OAI.AlgebraicGeometry.CycleClass.Thom.TorAlgebra.ExactLength
import OAI.AlgebraicGeometry.CycleClass.Thom.TorAlgebra.BoundedResolution

/-! # Euler -/

namespace OAI.AlgebraicGeometry.CycleClass.Thom.TorAlgebra.Euler

noncomputable section

/-! Additivity of the actual finite Tor Euler characteristic in a short
exact sequence. Finiteness and vanishing assumptions are stated on native
Tor modules, so this lemma applies to the geometric local modules. -/

set_option backward.isDefEq.respectTransparency false

open _root_.CategoryTheory _root_.CategoryTheory.Limits

namespace Tor

open OAI.AlgebraicGeometry.CycleClass.Thom.TorAlgebra.ExactSequence.Tor OAI.AlgebraicGeometry.CycleClass.Thom.TorAlgebra.ExactLength

universe u

variable (R : Type u) [CommRing R]

def euler (M N : ModuleCat.{u} R) (d : ℕ) : ℚ :=
  ∑ i ∈ Finset.range (d + 1), (-1 : ℚ) ^ i *
    ExactLength.rationalLength R (((Tor (ModuleCat R) i).obj M).obj N)

def connectingLength (N : ModuleCat.{u} R) (S : ShortComplex (ModuleCat R))
    (hS : S.ShortExact) (n : ℕ) : ℚ :=
  ExactLength.rationalLength R (.of R (LinearMap.range (ExactSequence.Tor.connecting R N S hS n).hom))

theorem degree_zero (N : ModuleCat.{u} R) (S : ShortComplex (ModuleCat R))
    (hS : S.ShortExact)
    (h₁ : Module.length R (((Tor (ModuleCat R) 0).obj S.X₁).obj N) ≠ ⊤)
    (h₂ : Module.length R (((Tor (ModuleCat R) 0).obj S.X₂).obj N) ≠ ⊤) :
    ExactLength.rationalLength R (((Tor (ModuleCat R) 0).obj S.X₁).obj N) +
      ExactLength.rationalLength R (((Tor (ModuleCat R) 0).obj S.X₃).obj N) =
    ExactLength.rationalLength R (((Tor (ModuleCat R) 0).obj S.X₂).obj N) +
      connectingLength R N S hS 0 := by
  have ha := ExactLength.rationalLength_exact R _ (ExactSequence.Tor.exact_after_connecting R N S hS 0) h₁
  have hb := ExactLength.rationalLength_exact R _ (ExactSequence.Tor.exact_middle R N S hS 0) h₂
  let : Epi (((Tor (ModuleCat R) 0).map S.g).app N) := ExactSequence.Tor.epi_zero R N S hS
  have hc := ExactLength.rationalLength_range_of_epi R (((Tor (ModuleCat R) 0).map S.g).app N)
  change ExactLength.rationalLength R (((Tor (ModuleCat R) 0).obj S.X₁).obj N) =
    connectingLength R N S hS 0 + _ at ha
  change ExactLength.rationalLength R (((Tor (ModuleCat R) 0).obj S.X₂).obj N) =
    ExactLength.rationalLength R (.of R (LinearMap.range (((Tor (ModuleCat R) 0).map S.f).app N).hom)) +
      ExactLength.rationalLength R (.of R (LinearMap.range (((Tor (ModuleCat R) 0).map S.g).app N).hom)) at hb
  linarith

theorem degree_succ (N : ModuleCat.{u} R) (S : ShortComplex (ModuleCat R))
    (hS : S.ShortExact) (n : ℕ)
    (h₁ : Module.length R (((Tor (ModuleCat R) (n + 1)).obj S.X₁).obj N) ≠ ⊤)
    (h₂ : Module.length R (((Tor (ModuleCat R) (n + 1)).obj S.X₂).obj N) ≠ ⊤)
    (h₃ : Module.length R (((Tor (ModuleCat R) (n + 1)).obj S.X₃).obj N) ≠ ⊤) :
    ExactLength.rationalLength R (((Tor (ModuleCat R) (n + 1)).obj S.X₁).obj N) +
      ExactLength.rationalLength R (((Tor (ModuleCat R) (n + 1)).obj S.X₃).obj N) =
    ExactLength.rationalLength R (((Tor (ModuleCat R) (n + 1)).obj S.X₂).obj N) +
      connectingLength R N S hS (n + 1) + connectingLength R N S hS n := by
  have ha := ExactLength.rationalLength_exact R _ (ExactSequence.Tor.exact_after_connecting R N S hS (n + 1)) h₁
  have hb := ExactLength.rationalLength_exact R _ (ExactSequence.Tor.exact_middle R N S hS (n + 1)) h₂
  have hc := ExactLength.rationalLength_exact R _ (ExactSequence.Tor.exact_before_connecting R N S hS n) h₃
  dsimp only [ShortComplex.mk, ShortComplex.map_X₂, ShortComplex.map_f, ShortComplex.map_g,
    Functor.flip_obj_obj, Functor.flip_obj_map] at ha hb hc
  change ExactLength.rationalLength R (((Tor (ModuleCat R) (n + 1)).obj S.X₂).obj N) =
    ExactLength.rationalLength R (.of R (LinearMap.range (((Tor (ModuleCat R) (n + 1)).map S.f).app N).hom)) +
      ExactLength.rationalLength R (.of R (LinearMap.range (((Tor (ModuleCat R) (n + 1)).map S.g).app N).hom)) at hb
  unfold connectingLength
  linarith

theorem alternating_identity (a b c k : ℕ → ℚ)
    (h₀ : a 0 + c 0 = b 0 + k 0)
    (hs : ∀ n, a (n + 1) + c (n + 1) = b (n + 1) + k (n + 1) + k n)
    (d : ℕ) :
    (∑ i ∈ Finset.range (d + 1), (-1 : ℚ) ^ i * b i) =
      (∑ i ∈ Finset.range (d + 1), (-1 : ℚ) ^ i * a i) +
      (∑ i ∈ Finset.range (d + 1), (-1 : ℚ) ^ i * c i) - (-1 : ℚ) ^ d * k d := by
  induction d with
  | zero => simpa using (sub_eq_iff_eq_add.mpr h₀).symm
  | succ d ih =>
    simp only [Finset.sum_range_succ (n := d + 1)]
    rw [ih]
    simp only [pow_succ]
    linear_combination ((-1 : ℚ) ^ d) * hs d

theorem additivity (N : ModuleCat.{u} R) (S : ShortComplex (ModuleCat R))
    (hS : S.ShortExact) (d : ℕ)
    (h₁ : ∀ n, Module.length R (((Tor (ModuleCat R) n).obj S.X₁).obj N) ≠ ⊤)
    (h₂ : ∀ n, Module.length R (((Tor (ModuleCat R) n).obj S.X₂).obj N) ≠ ⊤)
    (h₃ : ∀ n, Module.length R (((Tor (ModuleCat R) n).obj S.X₃).obj N) ≠ ⊤)
    (hv : IsZero (((Tor (ModuleCat R) (d + 1)).obj S.X₃).obj N)) :
    euler R S.X₂ N d = euler R S.X₁ N d + euler R S.X₃ N d := by
  have h := alternating_identity
    (fun n => ExactLength.rationalLength R (((Tor (ModuleCat R) n).obj S.X₁).obj N))
    (fun n => ExactLength.rationalLength R (((Tor (ModuleCat R) n).obj S.X₂).obj N))
    (fun n => ExactLength.rationalLength R (((Tor (ModuleCat R) n).obj S.X₃).obj N))
    (connectingLength R N S hS) (degree_zero R N S hS (h₁ 0) (h₂ 0))
    (fun n => degree_succ R N S hS n (h₁ _) (h₂ _) (h₃ _)) d
  have hk : connectingLength R N S hS d = 0 :=
    ExactLength.rationalLength_range_of_zero R _ (hv.eq_of_src _ _)
  simpa only [euler, hk, mul_zero, sub_zero] using h

end Tor

end

end OAI.AlgebraicGeometry.CycleClass.Thom.TorAlgebra.Euler

import OAI.AlgebraicGeometry.GroupSchemes.ConnectedTower
import OAI.AlgebraicGeometry.GroupSchemes.SplitAlgebra

/-! # Prime Dichotomy -/

namespace OAI.AlgebraicGeometry.GroupSchemes

noncomputable section

/-! A prime-order group scheme killed by p is connected or split étale. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry Opposite WithConv _root_.CategoryTheory.MonObj

universe u
variable {k : Type u} [Field k] [IsAlgClosed k]

section

/-- A rank-p group with p-torsion rational points is local or split étale. -/
theorem FiniteEtale.FiniteCommGroupScheme.local_or_split (G : FiniteEtale.FiniteCommGroupScheme k) (p : ℕ) [Fact p.Prime]
    (hdim : Module.finrank k G.algebra = p)
    (hpow : ∀ x : FiniteEtale.affine k (CommAlgCat.of k k) ⟶ G.scheme, x ^ p = 1) :
    IsLocalRing G.algebra ∨ Algebra.IsFiniteSplit k G.algebra := by
  by_cases hlocal : IsLocalRing G.algebra
  · exact Or.inl hlocal
  right
  obtain ⟨x, hx⟩ : ∃ x : FiniteEtale.affine k (CommAlgCat.of k k) ⟶ G.scheme, x ≠ 1 := by
    by_contra h
    push Not at h
    exact hlocal (G.local_of_point_eq_one h)
  have horder : orderOf x = p := orderOf_eq_prime (hpow x) hx
  let f : Fin p → G.algebra →ₐ[k] k :=
    fun i => ((G.coordinatePoints (CommAlgCat.of k k)).symm (x ^ (i : ℕ))).ofConv
  have hf : Function.Injective f := by
    intro i j hij
    have he : (G.coordinatePoints (CommAlgCat.of k k)).symm (x ^ (i : ℕ)) =
        (G.coordinatePoints (CommAlgCat.of k k)).symm (x ^ (j : ℕ)) :=
      WithConv.ofConv_injective hij
    have hp := (G.coordinatePoints (CommAlgCat.of k k)).symm.injective he
    apply Fin.ext
    exact pow_injOn_Iio_orderOf (by simpa only [horder, Set.mem_Iio] using i.isLt)
      (by simpa only [horder, Set.mem_Iio] using j.isLt) hp
  exact ⟨p, ⟨SplitAlgebra.FiniteEtale.evaluationEquiv k G.algebra f hf
    (by simpa only [Fintype.card_fin] using hdim.symm)⟩⟩

end

/-- The first level of a height-one p-divisible group is connected or split étale. -/
theorem FiniteEtale.PDivisibleGroup.first_local_or_split {p : ℕ} [Fact p.Prime]
    (G : FiniteEtale.PDivisibleGroup k p 1) :
    IsLocalRing (G.level 1).algebra ∨ Algebra.IsFiniteSplit k (G.level 1).algebra := by
  apply (G.level 1).local_or_split p
  · simpa only [Nat.mul_one, pow_one] using G.rank 1
  · intro x
    simpa only [pow_one] using G.annihilated k 1 (CommAlgCat.of k k) x

end

end OAI.AlgebraicGeometry.GroupSchemes

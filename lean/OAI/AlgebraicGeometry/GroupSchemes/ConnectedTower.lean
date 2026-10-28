import OAI.AlgebraicGeometry.GroupSchemes.FiniteAlgebra
import OAI.AlgebraicGeometry.GroupSchemes.ConnectedStep

/-! # Connected Tower -/

namespace OAI.AlgebraicGeometry.GroupSchemes

noncomputable section

/-! Connectedness propagates from the first level throughout the actual tower. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry Opposite WithConv _root_.CategoryTheory.MonObj

universe u
variable {k : Type u} [Field k]

section

/-- A finite group scheme with local coordinate algebra has only the identity rational point. -/
theorem FiniteEtale.FiniteCommGroupScheme.point_eq_one_of_local (G : FiniteEtale.FiniteCommGroupScheme k) [IsLocalRing G.algebra]
    (x : FiniteEtale.affine k (CommAlgCat.of k k) ⟶ G.scheme) : x = 1 := by
  let f : G.algebra →ₐ[k] k := ((G.coordinatePoints (CommAlgCat.of k k)).symm x).ofConv
  have hf := FiniteAlgebra.EtaleFinite.point_eq_of_local k G.algebra G.coordinateAugmentation f
  calc
    x = G.coordinatePoints (CommAlgCat.of k k) (toConv f) :=
      ((G.coordinatePoints (CommAlgCat.of k k)).apply_symm_apply x).symm
    _ = G.coordinatePoints (CommAlgCat.of k k) (toConv G.coordinateAugmentation) :=
      congrArg (fun a => G.coordinatePoints (CommAlgCat.of k k) (toConv a)) hf
    _ = 1 := (G.coordinatePoints (CommAlgCat.of k k)).map_one

/-- Over an algebraically closed field, having only the identity point implies locality. -/
theorem FiniteEtale.FiniteCommGroupScheme.local_of_point_eq_one [IsAlgClosed k] (G : FiniteEtale.FiniteCommGroupScheme k)
    (hx : ∀ x : FiniteEtale.affine k (CommAlgCat.of k k) ⟶ G.scheme, x = 1) : IsLocalRing G.algebra := by
  apply FiniteAlgebra.EtaleFinite.isLocalRing_of_unique_point k G.algebra G.coordinateAugmentation
  intro f
  apply WithConv.toConv_injective
  apply (G.coordinatePoints (CommAlgCat.of k k)).injective
  exact (hx _).trans (G.coordinatePoints (CommAlgCat.of k k)).map_one.symm

end

/-- Once the first level has no nonidentity rational point, neither does any later level. -/
theorem FiniteEtale.PDivisibleGroup.points_eq_one_of_first_local {p h : ℕ} (G : FiniteEtale.PDivisibleGroup k p h)
    (hfirst : IsLocalRing (G.level 1).algebra) :
    ∀ n, ∀ x : FiniteEtale.affine k (CommAlgCat.of k k) ⟶ (G.level n).scheme, x = 1 := by
  intro n
  cases n with
  | zero =>
    intro x
    simpa only [pow_zero, pow_one] using G.annihilated k 0 (CommAlgCat.of k k) x
  | succ n =>
    induction n with
    | zero =>
      have := hfirst
      exact (G.level 1).point_eq_one_of_local
    | succ n ih =>
      intro x
      have hkernel : ∀ z : FiniteEtale.affine k (CommAlgCat.of k k) ⟶ (G.level (n + 1 + 1)).scheme,
          z ^ (p ^ (n + 1)) = 1 → z = 1 := by
        intro z hz
        obtain ⟨y, hy⟩ := (G.kernel (n + 1) (CommAlgCat.of k k) z).mpr hz
        rw [← hy, ih y, MonObj.one_comp]
      have hxp : x ^ p = 1 := by
        apply hkernel
        rw [← pow_mul, ← pow_succ']
        exact G.annihilated k (n + 1 + 1) (CommAlgCat.of k k) x
      apply hkernel
      rw [pow_succ', pow_mul, hxp, one_pow]

/-- A local first level forces all levels to have local coordinate algebras. -/
theorem FiniteEtale.PDivisibleGroup.local_of_first_local [IsAlgClosed k] {p h : ℕ} (G : FiniteEtale.PDivisibleGroup k p h)
    (hfirst : IsLocalRing (G.level 1).algebra) (n : ℕ) : IsLocalRing (G.level n).algebra :=
  (G.level n).local_of_point_eq_one (G.points_eq_one_of_first_local hfirst n)

/-- In height one, a connected first level has a nonlocal Cartier dual. -/
theorem FiniteEtale.PDivisibleGroup.dual_not_local_of_first_local [IsAlgClosed k] {p : ℕ}
    [Fact p.Prime] [CharP k p] (G : FiniteEtale.PDivisibleGroup k p 1)
    (hfirst : IsLocalRing (G.level 1).algebra) :
    ¬ IsLocalRing (G.level 1).cartierDual.algebra :=
  G.not_local_local (G.local_of_first_local hfirst 2)

end

end OAI.AlgebraicGeometry.GroupSchemes

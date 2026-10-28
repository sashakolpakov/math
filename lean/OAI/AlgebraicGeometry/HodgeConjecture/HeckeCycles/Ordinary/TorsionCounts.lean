import OAI.AlgebraicGeometry.Picard.Homomorphisms.OrdinaryDivision
import OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.TorsionTower
import Mathlib.GroupTheory.Index

/-! # Torsion Counts -/

namespace OAI

noncomputable section

namespace AlgebraicGeometry.HodgeConjecture.HeckeCycles.Ordinary.TorsionCounts.CM.OrdinaryDivision

/-! The actual ordinary p-rank supplies division in every geometric
torsion level. This is derived from the proper connected group and its
finite p-torsion, without assuming an ordinary coordinate splitting. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj
open OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.TorsionTower.Construction

theorem torsionTower_surjective_of_division {A : Type*} [CommGroup A]
    (q n : ℕ) (hdiv : Function.Surjective (fun a : A => a ^ q)) :
    Function.Surjective (AbelianScheme.FrobeniusKernel.TorsionTower.Construction.torsionTowerReduction A q n) := by
  intro x
  obtain ⟨y, hy⟩ := hdiv x.val
  change y ^ q = x.val at hy
  have hpow : y ^ (q ^ (n + 1)) = 1 := by
    rw [pow_succ', pow_mul, hy]
    exact x.property
  exact ⟨⟨y, hpow⟩, Subtype.ext hy⟩

variable {k : Type} [Field k] [IsAlgClosed k]
  (A : Over (Spec (.of k))) [GrpObj A] [IsCommMonObj A]
  [Smooth A.hom] [IsProper A.hom] [GeometricallyConnected A.hom]
  (q : ℕ) [Fact q.Prime] (g : ℕ)

theorem ordinary_torsionTower_surjective
    (hordinary : Nat.card (powMonoidHom q :
      (Over.mk (𝟙 (Spec (.of k))) ⟶ A) →* _).ker = q ^ g) (n : ℕ) :
    Function.Surjective (AbelianScheme.FrobeniusKernel.TorsionTower.Construction.torsionTowerReduction
      (Over.mk (𝟙 (Spec (.of k))) ⟶ A) q n) := by
  let : Finite (powMonoidHom q :
      (Over.mk (𝟙 (Spec (.of k))) ⟶ A) →* _).ker :=
    Nat.finite_of_card_ne_zero
      (hordinary ▸ pow_ne_zero g (Fact.out : q.Prime).ne_zero)
  exact torsionTower_surjective_of_division q n
    (Picard.Homomorphisms.OrdinaryDivision.Construction.rational_points_divisible_of_finite_torsion A q)

end AlgebraicGeometry.HodgeConjecture.HeckeCycles.Ordinary.TorsionCounts.CM.OrdinaryDivision

namespace AlgebraicGeometry.HodgeConjecture.HeckeCycles.Ordinary.TorsionCounts.CM

/-! The actual ordinary p-rank determines every geometric p-power
torsion count. The proof uses the kernel of each division map, rather
than assuming a torsion-coordinate isomorphism. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj
open OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.TorsionTower.Construction

variable {A : Type*} [CommGroup A]

def torsionTowerKernelEquiv (q n : ℕ) :
    (AbelianScheme.FrobeniusKernel.TorsionTower.Construction.torsionTowerReduction A q n).ker ≃ AbelianScheme.FrobeniusKernel.OrdinaryIsogeny.Construction.qTorsion A q where
  toFun x := ⟨x.val.val, congrArg Subtype.val x.property⟩
  invFun x := ⟨⟨x.val, by
    change x.val ^ (q ^ (n + 1)) = 1
    rw [pow_succ', pow_mul]
    have hx : x.val ^ q = 1 := x.property
    rw [hx, one_pow]⟩, Subtype.ext x.property⟩
  left_inv _ := rfl
  right_inv _ := rfl

theorem torsionTower_card_step (q n : ℕ)
    (hsurj : Function.Surjective (AbelianScheme.FrobeniusKernel.TorsionTower.Construction.torsionTowerReduction A q n)) :
    Nat.card (AbelianScheme.FrobeniusKernel.OrdinaryIsogeny.Construction.qTorsion A (q ^ (n + 1))) =
      Nat.card (AbelianScheme.FrobeniusKernel.OrdinaryIsogeny.Construction.qTorsion A q) * Nat.card (AbelianScheme.FrobeniusKernel.OrdinaryIsogeny.Construction.qTorsion A (q ^ n)) := by
  let f := AbelianScheme.FrobeniusKernel.TorsionTower.Construction.torsionTowerReduction A q n
  have h := f.ker.card_mul_index
  rw [Subgroup.index_ker, f.range_eq_top_of_surjective hsurj, Subgroup.card_top] at h
  exact h.symm.trans (congrArg (· * Nat.card (AbelianScheme.FrobeniusKernel.OrdinaryIsogeny.Construction.qTorsion A (q ^ n)))
    (Nat.card_congr (torsionTowerKernelEquiv (A := A) q n)))

theorem torsionTower_card (q g : ℕ)
    (hcard : Nat.card (AbelianScheme.FrobeniusKernel.OrdinaryIsogeny.Construction.qTorsion A q) = q ^ g)
    (hsurj : ∀ n, Function.Surjective (AbelianScheme.FrobeniusKernel.TorsionTower.Construction.torsionTowerReduction A q n)) (n : ℕ) :
    Nat.card (AbelianScheme.FrobeniusKernel.OrdinaryIsogeny.Construction.qTorsion A (q ^ n)) = q ^ (n * g) := by
  induction n with
  | zero =>
    have : Subsingleton (AbelianScheme.FrobeniusKernel.OrdinaryIsogeny.Construction.qTorsion A (q ^ 0)) := ⟨fun x y => Subtype.ext (by
      have hx0 : x.val ^ (q ^ 0) = 1 := x.property
      have hy0 : y.val ^ (q ^ 0) = 1 := y.property
      have hx : x.val = 1 := by simpa only [pow_zero, pow_one] using hx0
      have hy : y.val = 1 := by simpa only [pow_zero, pow_one] using hy0
      exact hx.trans hy.symm)⟩
    rw [Nat.zero_mul]
    exact Nat.card_unique
  | succ n ih =>
    rw [torsionTower_card_step q n (hsurj n), hcard, ih, Nat.succ_mul, pow_add]
    exact Nat.mul_comm _ _

variable {k : Type} [Field k] [IsAlgClosed k]
  (B : Over (Spec (.of k))) [GrpObj B] [IsCommMonObj B]
  [Smooth B.hom] [IsProper B.hom] [GeometricallyConnected B.hom]
  (q : ℕ) [Fact q.Prime] (g : ℕ)

theorem ordinary_torsionTower_card
    (hordinary : Nat.card (powMonoidHom q :
      (Over.mk (𝟙 (Spec (.of k))) ⟶ B) →* _).ker = q ^ g) (n : ℕ) :
    Nat.card (AbelianScheme.FrobeniusKernel.OrdinaryIsogeny.Construction.qTorsion (Over.mk (𝟙 (Spec (.of k))) ⟶ B) (q ^ n)) = q ^ (n * g) :=
  torsionTower_card q g hordinary
    (OrdinaryDivision.ordinary_torsionTower_surjective B q g hordinary) n

end AlgebraicGeometry.HodgeConjecture.HeckeCycles.Ordinary.TorsionCounts.CM

end

end OAI

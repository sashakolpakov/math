import OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.GeometricIsogeny
import Mathlib.Data.ZMod.Basic

/-! # Torsion Tower -/

namespace OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.TorsionTower.Construction

noncomputable section

/-!
Division of geometric kernel points from the ordinary torsion tower.
Only this q-rank argument uses geometric point groups. Scheme kernels and
their annihilators continue to use the fppf constructions in the other
FrobeniusKernel modules, retaining their multiplicative and nonreduced structure.
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

variable {A : Type*} [CommGroup A]

/-- Multiplication by q from level n+1 to level n of the actual torsion. -/
def torsionTowerReduction (A : Type*) [CommGroup A] (q n : ℕ) :
    OrdinaryIsogeny.Construction.qTorsion A (q ^ (n + 1)) →* OrdinaryIsogeny.Construction.qTorsion A (q ^ n) where
  toFun x := ⟨x.val ^ q, by
    change (x.val ^ q) ^ (q ^ n) = 1
    rw [← pow_mul, ← pow_succ']
    exact x.property⟩
  map_one' := Subtype.ext (one_pow q)
  map_mul' x y := Subtype.ext (mul_pow x.val y.val q)

def etaleTowerReduction (q n r : ℕ) :
    Multiplicative (Fin r → ZMod (q ^ (n + 1))) →*
      Multiplicative (Fin r → ZMod (q ^ n)) where
  toFun x := Multiplicative.ofAdd (fun i =>
    ZMod.castHom (show q ^ n ∣ q ^ (n + 1) from ⟨q, pow_succ q n⟩)
      (ZMod (q ^ n)) (x.toAdd i))
  map_one' := by
    apply Multiplicative.toAdd.injective
    funext i
    exact (ZMod.castHom (show q ^ n ∣ q ^ (n + 1) from ⟨q, pow_succ q n⟩)
      (ZMod (q ^ n))).map_zero
  map_mul' x y := by
    apply Multiplicative.toAdd.injective
    funext i
    exact (ZMod.castHom (show q ^ n ∣ q ^ (n + 1) from ⟨q, pow_succ q n⟩)
      (ZMod (q ^ n))).map_add (x.toAdd i) (y.toAdd i)

theorem etaleTowerReduction_surjective (q n r : ℕ) :
    Function.Surjective (etaleTowerReduction q n r) := by
  intro x
  have h : q ^ n ∣ q ^ (n + 1) := ⟨q, pow_succ q n⟩
  choose y hy using fun i : Fin r => ZMod.castHom_surjective h (x.toAdd i)
  refine ⟨Multiplicative.ofAdd y, ?_⟩
  apply Multiplicative.toAdd.injective
  exact funext hy

/-- The geometric-point consequence of a compatible ordinary splitting.
The multiplicative factors have only their identity as an algebraically
closed point in characteristic q; the r étale factors give this tower.
No assertion about scheme-theoretic kernels is part of this structure. -/
structure GeometricEtaleTorsionTower (A : Type*) [CommGroup A] (q r : ℕ) where
  equiv : ∀ n, OrdinaryIsogeny.Construction.qTorsion A (q ^ n) ≃* Multiplicative (Fin r → ZMod (q ^ n))
  compatible : ∀ n (x : OrdinaryIsogeny.Construction.qTorsion A (q ^ (n + 1))),
    equiv n (torsionTowerReduction A q n x) = etaleTowerReduction q n r (equiv (n + 1) x)

theorem GeometricEtaleTorsionTower.reduction_surjective {q r : ℕ}
    (t : GeometricEtaleTorsionTower A q r) (n : ℕ) :
    Function.Surjective (torsionTowerReduction A q n) := by
  intro x
  obtain ⟨y, hy⟩ := etaleTowerReduction_surjective q n r (t.equiv n x)
  refine ⟨(t.equiv (n + 1)).symm y, (t.equiv n).injective ?_⟩
  rw [t.compatible, MulEquiv.apply_symm_apply, hy]

/-- A q-power torsion point has a q-division lift in the source group. -/
theorem GeometricEtaleTorsionTower.divide {q r : ℕ}
    (t : GeometricEtaleTorsionTower A q r) (n : ℕ) (a : A) (ha : a ^ (q ^ n) = 1) :
    ∃ b : A, b ^ q = a := by
  obtain ⟨b, hb⟩ := t.reduction_surjective n ⟨a, ha⟩
  exact ⟨b.val, congrArg Subtype.val hb⟩

/-- The ordinary torsion-tower splitting keeps the quotient by any q-power
kernel on the same q-rank stratum. -/
theorem isogeny_qRank_preserved_of_ordinary_tower
    {K : Type u} [Field K] [IsAlgClosed K] {g h : ℕ} {S : Scheme.{u}}
    {A : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g S} {B : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme h S}
    (f : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme.Isogeny A B) (s : Spec (.of K) ⟶ S)
    (q n r : ℕ) (t : GeometricEtaleTorsionTower (A.Points (Over.mk s)) q r)
    (hkernel : ∀ k : f.kernelAt (Over.mk s), k.val ^ (q ^ n) = 1) :
    Nat.card (A.torsionPoints q (Over.mk s)) =
      Nat.card (B.torsionPoints q (Over.mk s)) :=
  GeometricIsogeny.Construction.isogeny_geometric_qRank_preserved f s q (fun k => t.divide n k.val (hkernel k))

end

end OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.TorsionTower.Construction

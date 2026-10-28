import OAI.AlgebraicGeometry.AbelianScheme.TateComparison.PELIsogenies
import Mathlib.Algebra.Module.ZMod
import Mathlib.NumberTheory.Padics.RingHoms

/-! # Add -/

namespace OAI.AlgebraicGeometry.AbelianScheme.TateComparison.Add

noncomputable section

/-!
The Tate module is constructed from the actual torsion points of a group
scheme. Its p-adic scalar action comes from the residue maps Z_p -> Z/p^n;
its transition maps are multiplication by p. No free-rank assertion,
Tate frame, polarization pairing, or isogeny comparison is assumed.
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj

universe u

namespace Tate

variable (q : ℕ) [Fact q.Prime] (H : Type u) [AddCommGroup H]

/-- The subgroup killed by q^n. -/
def torsion (n : ℕ) : AddSubgroup H where
  carrier := {x | q ^ n • x = 0}
  zero_mem' := nsmul_zero _
  add_mem' hx hy := by
    simp only [Set.mem_ofPred_eq] at hx hy ⊢
    rw [nsmul_add, hx, hy, add_zero]
  neg_mem' hx := by
    simp only [Set.mem_ofPred_eq] at hx ⊢
    rw [smul_neg, hx, neg_zero]

omit [Fact q.Prime] in
@[simp] theorem mem_torsion (n : ℕ) (x : H) : x ∈ torsion q H n ↔ q ^ n • x = 0 :=
  Iff.rfl

instance torsion_zmodModule (n : ℕ) : Module (ZMod (q ^ n)) (torsion q H n) :=
  AddCommGroup.zmodModule (fun x => Subtype.ext x.property)

instance torsion_padicModule (n : ℕ) : Module ℤ_[q] (torsion q H n) :=
  Module.compHom _ (PadicInt.toZModPow n)

variable {H} {H' : Type u} [AddCommGroup H']

/-- Every additive map between these torsion groups commutes with p-adic
scalars when its target exponent is no larger than its source exponent. -/
theorem map_padic_smul {m n : ℕ} (hmn : m ≤ n)
    (f : torsion q H n →+ torsion q H' m) (z : ℤ_[q]) (x : torsion q H n) :
    f (z • x) = z • f x := by
  change f (PadicInt.toZModPow n z • x) = PadicInt.toZModPow m z • f x
  have hz : ((PadicInt.toZModPow n z).val : ZMod (q ^ m)) =
      PadicInt.toZModPow m z := by
    have h := congrArg (fun a : ℤ_[q] →+* ZMod (q ^ m) => a z)
      (PadicInt.zmod_cast_comp_toZModPow m n hmn)
    let castMap := ZMod.castHom (pow_dvd_pow q hmn) (ZMod (q ^ m))
    have hnat := map_natCast castMap (PadicInt.toZModPow n z).val
    have hcast := congrArg castMap (ZMod.natCast_zmod_val (PadicInt.toZModPow n z))
    exact hnat.symm.trans (hcast.trans h)
  conv_lhs => rw [← ZMod.natCast_zmod_val (PadicInt.toZModPow n z)]
  rw [Nat.cast_smul_eq_nsmul, map_nsmul, ← hz, Nat.cast_smul_eq_nsmul]

/-- Multiplication by q takes q^(n+1)-torsion into q^n-torsion. -/
def transitionAdd (n : ℕ) : torsion q H (n + 1) →+ torsion q H n where
  toFun x := ⟨q • x.val, by
    change q ^ n • (q • x.val) = 0
    rw [← mul_nsmul, ← pow_succ']
    exact x.property⟩
  map_zero' := Subtype.ext (nsmul_zero _)
  map_add' x y := Subtype.ext (nsmul_add _ _ _)

def transition (n : ℕ) : torsion q H (n + 1) →ₗ[ℤ_[q]] torsion q H n :=
  { transitionAdd q n with
    map_smul' z x := map_padic_smul q (Nat.le_succ n) (transitionAdd q n) z x }

/-- The inverse limit of the actual torsion groups. -/
def compatible : Submodule ℤ_[q] (∀ n, torsion q H n) where
  carrier := {x | ∀ n, transition q n (x (n + 1)) = x n}
  zero_mem' n := map_zero _
  add_mem' hx hy n := by rw [Pi.add_apply, map_add, hx n, hy n]; rfl
  smul_mem' z x hx n := by rw [Pi.smul_apply, map_smul, hx n]; rfl

abbrev Module := compatible (H := H) q

/-- A homomorphism of point groups acts on every torsion level. -/
def mapLevel (f : H →+ H') (n : ℕ) : torsion q H n →ₗ[ℤ_[q]] torsion q H' n :=
  let F : torsion q H n →+ torsion q H' n := {
    toFun x := ⟨f x.val, by
      change q ^ n • f x.val = 0
      rw [← map_nsmul, x.property, map_zero]⟩
    map_zero' := Subtype.ext f.map_zero
    map_add' x y := Subtype.ext (f.map_add x.val y.val) }
  { F with map_smul' z x := map_padic_smul q le_rfl F z x }

theorem mapLevel_transition (f : H →+ H') (n : ℕ) (x : torsion q H (n + 1)) :
    mapLevel q f n (transition q n x) = transition q n (mapLevel q f (n + 1) x) :=
  Subtype.ext (f.map_nsmul q x.val)

/-- The induced map of Tate modules is constructed level by level. -/
def map (f : H →+ H') : Tate.Module (H := H) q →ₗ[ℤ_[q]] Tate.Module (H := H') q where
  toFun x := ⟨fun n => mapLevel q f n (x.val n), by
    intro n
    rw [← mapLevel_transition, x.property n]⟩
  map_add' x y := Subtype.ext (funext fun n => (mapLevel q f n).map_add _ _)
  map_smul' z x := Subtype.ext (funext fun n => (mapLevel q f n).map_smul z _)

end Tate

variable {S : Scheme.{u}} (A : Over S) [GrpObj A] [IsCommMonObj A]
  (T : Over S) (q : ℕ) [Fact q.Prime]

/-- The q-adic Tate module of the actual T-valued points of A. -/
abbrev schemeTateModule := Tate.Module (H := Additive (T ⟶ A)) q

/-- Every algebraic group morphism acts on the constructed Tate modules. -/
def schemeTateMap {B : Over S} [GrpObj B] [IsCommMonObj B]
    (f : A ⟶ B) [IsMonHom f] :
    schemeTateModule A T q →ₗ[ℤ_[q]] schemeTateModule B T q :=
  let fpts : (T ⟶ A) →* (T ⟶ B) := {
    toFun x := x ≫ f
    map_one' := MonObj.one_comp f
    map_mul' x y := MonObj.mul_comp x y f }
  Tate.map q fpts.toAdditive

end

end OAI.AlgebraicGeometry.AbelianScheme.TateComparison.Add

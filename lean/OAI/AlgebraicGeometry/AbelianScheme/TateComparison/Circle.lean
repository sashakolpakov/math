import OAI.AlgebraicGeometry.AbelianScheme.TateComparison.PadicResidueLimit
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.TorsionCongruence

/-! # Circle -/

namespace OAI.AlgebraicGeometry.AbelianScheme.TateComparison.Circle

noncomputable section

/-! The Tate module of the actual real circle, through its compatible
torsion coordinates and the p-adic residue limit. -/

open OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.TorsionCongruence.TorusTorsion
variable (q : ℕ) [Fact q.Prime]

theorem circle_pow_cast (m n : ℕ) (z : ZMod (q ^ (m + n))) :
    q ^ n • ZMod.toAddCircle z =
      ZMod.toAddCircle (ZMod.castHom (pow_dvd_pow q (Nat.le_add_right m n)) (ZMod (q ^ m)) z) := by
  obtain ⟨a, rfl⟩ := ZMod.intCast_surjective z
  rw [map_intCast (ZMod.castHom (pow_dvd_pow q (Nat.le_add_right m n)) (ZMod (q ^ m))),
    ZMod.toAddCircle_intCast, ZMod.toAddCircle_intCast, ← AddCircle.coe_nsmul,
    nsmul_eq_mul]
  congr 1
  have hq : (q : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Fact.out : q.Prime).ne_zero
  push_cast
  rw [pow_add]
  field_simp

def circleTorsionEquiv (n : ℕ) : ZMod (q ^ n) ≃+ Add.Tate.torsion q UnitAddCircle n :=
  AbelianModuli.ReferenceFamily.TorsionCongruence.TorusTorsion.circleEquiv (q ^ n)

theorem circleTorsionEquiv_transition (n : ℕ) (z : ZMod (q ^ (n + 1))) :
    Add.Tate.transition q n (circleTorsionEquiv q (n + 1) z) =
      circleTorsionEquiv q n (ZMod.castHom (pow_dvd_pow q (Nat.le_succ n)) _ z) := by
  apply Subtype.ext
  change q • ZMod.toAddCircle z =
    ZMod.toAddCircle (ZMod.castHom (pow_dvd_pow q (Nat.le_succ n)) (ZMod (q ^ n)) z)
  simpa only [pow_one] using circle_pow_cast q n 1 z

def padicToCircleTate : ℤ_[q] →ₗ[ℤ_[q]] Add.Tate.Module (H := UnitAddCircle) q where
  toFun z := ⟨fun n => circleTorsionEquiv q n (PadicInt.toZModPow n z), by
    intro n
    rw [circleTorsionEquiv_transition]
    exact congrArg (circleTorsionEquiv q n)
      (congrArg (fun f : ℤ_[q] →+* ZMod (q ^ n) => f z)
        (PadicInt.zmod_cast_comp_toZModPow n (n + 1) (Nat.le_succ n)))⟩
  map_add' x y := by
    apply Subtype.ext
    funext n
    exact (congrArg (circleTorsionEquiv q n) ((PadicInt.toZModPow n).map_add x y)).trans
      ((circleTorsionEquiv q n).map_add _ _)
  map_smul' z x := by
    apply Subtype.ext
    funext n
    change circleTorsionEquiv q n (PadicInt.toZModPow n (z * x)) =
      PadicInt.toZModPow n z • circleTorsionEquiv q n (PadicInt.toZModPow n x)
    rw [map_mul, ← ZMod.natCast_zmod_val (PadicInt.toZModPow n z),
      ← nsmul_eq_mul, Nat.cast_smul_eq_nsmul, map_nsmul]

def circleTateResidues (x : Add.Tate.Module (H := UnitAddCircle) q) : PadicResidueLimit.compatibleResidues q := by
  let c := fun n => (circleTorsionEquiv q n).symm (x.val n)
  have hc (n : ℕ) : ZMod.toAddCircle (c n) = (x.val n).val :=
    congrArg Subtype.val ((circleTorsionEquiv q n).apply_symm_apply (x.val n))
  refine ⟨c, ?_⟩
  intro m n h
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le h
  apply ZMod.toAddCircle_injective
  rw [← circle_pow_cast, hc, hc]
  exact Functor.Tate.transition_iterate q x m d

theorem padicToCircleTate_bijective : Function.Bijective (padicToCircleTate q) := by
  constructor
  · intro z w h
    apply PadicInt.ext_of_toZModPow.mp
    intro n
    exact (circleTorsionEquiv q n).injective
      (congrArg (fun x : Add.Tate.Module (H := UnitAddCircle) q => x.val n) h)
  · intro x
    refine ⟨PadicResidueLimit.padicResidueLimit q (circleTateResidues q x), ?_⟩
    apply Subtype.ext
    funext n
    change circleTorsionEquiv q n
      (PadicInt.toZModPow n (PadicResidueLimit.padicResidueLimit q (circleTateResidues q x))) = x.val n
    rw [PadicResidueLimit.padicResidueLimit_spec]
    exact (circleTorsionEquiv q n).apply_symm_apply (x.val n)

def circleTateEquiv : ℤ_[q] ≃ₗ[ℤ_[q]] Add.Tate.Module (H := UnitAddCircle) q :=
  LinearEquiv.ofBijective (padicToCircleTate q) (padicToCircleTate_bijective q)

end

end OAI.AlgebraicGeometry.AbelianScheme.TateComparison.Circle

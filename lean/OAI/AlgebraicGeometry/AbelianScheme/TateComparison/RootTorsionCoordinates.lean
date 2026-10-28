import OAI.AlgebraicGeometry.AbelianScheme.TateComparison.CompatibleRootsOfUnity
import OAI.AlgebraicGeometry.AbelianScheme.TateComparison.Add

/-! # Root Torsion Coordinates -/

namespace OAI.AlgebraicGeometry.AbelianScheme.TateComparison.RootTorsionCoordinates

noncomputable section

/-! Compatible primitive roots give additive residue coordinates on
the actual q-power torsion in the multiplicative group of the field. -/

variable (q : ℕ) [Fact q.Prime] {k : Type*} [Field k]

private instance qPower_neZero (n : ℕ) : NeZero (q ^ n) :=
  ⟨pow_ne_zero n (Fact.out : q.Prime).ne_zero⟩

def primitiveRootTorsionEquiv (n : ℕ) (ζ : kˣ) (hζ : IsPrimitiveRoot ζ (q ^ n)) :
    ZMod (q ^ n) ≃+ Add.Tate.torsion q (Additive kˣ) n where
  toFun a := ⟨Additive.ofMul (hζ.zmodEquivZPowers a).toMul.val, by
    change (hζ.zmodEquivZPowers a).toMul.val ^ (q ^ n) = 1
    have h := (hζ.zmodEquivZPowers a).toMul.property
    exact (le_of_eq hζ.zpowers_eq) h⟩
  invFun a := hζ.zmodEquivZPowers.symm
    (Additive.ofMul ⟨a.val.toMul, by
      rw [hζ.zpowers_eq]
      exact a.property⟩)
  left_inv a := by
    exact hζ.zmodEquivZPowers.symm_apply_apply a
  right_inv a := by
    apply Subtype.ext
    exact congrArg (fun z : Additive (Subgroup.zpowers ζ) => Additive.ofMul z.toMul.val)
      (hζ.zmodEquivZPowers.apply_symm_apply
        (Additive.ofMul ⟨a.val.toMul, by rw [hζ.zpowers_eq]; exact a.property⟩))
  map_add' a b := by
    apply Subtype.ext
    exact congrArg (fun z : Additive (Subgroup.zpowers ζ) => Additive.ofMul z.toMul.val)
      (hζ.zmodEquivZPowers.map_add a b)

theorem primitiveRootTorsionEquiv_natCast (n : ℕ) (ζ : kˣ) (hζ : IsPrimitiveRoot ζ (q ^ n)) (i : ℕ) :
    (primitiveRootTorsionEquiv q n ζ hζ (i : ZMod (q ^ n))).val.toMul = ζ ^ i := by
  change (hζ.zmodEquivZPowers (i : ZMod (q ^ n))).toMul.val = ζ ^ i
  rw [hζ.zmodEquivZPowers_apply_coe_nat]
  rfl

variable (k) [CharZero k] [IsAlgClosed k]

def compatiblePrimitiveRootUnit (n : ℕ) : kˣ :=
  Units.mk0 (CompatibleRootsOfUnity.compatiblePrimitiveRoots q k n).val
    ((CompatibleRootsOfUnity.compatiblePrimitiveRoots q k n).property.ne_zero (NeZero.ne (q ^ n)))

theorem compatiblePrimitiveRootUnit_primitive (n : ℕ) :
    IsPrimitiveRoot (compatiblePrimitiveRootUnit q k n) (q ^ n) :=
  IsPrimitiveRoot.coe_units_iff.mp (CompatibleRootsOfUnity.compatiblePrimitiveRoots q k n).property

theorem compatiblePrimitiveRootUnit_pow (n : ℕ) :
    compatiblePrimitiveRootUnit q k (n + 1) ^ q = compatiblePrimitiveRootUnit q k n := by
  apply Units.ext
  exact CompatibleRootsOfUnity.compatiblePrimitiveRoots_pow q k n

def rootTorsionEquiv (n : ℕ) : ZMod (q ^ n) ≃+ Add.Tate.torsion q (Additive kˣ) n :=
  primitiveRootTorsionEquiv q n (compatiblePrimitiveRootUnit q k n)
    (compatiblePrimitiveRootUnit_primitive q k n)

theorem rootTorsionEquiv_transition (n : ℕ) (z : ZMod (q ^ (n + 1))) :
    Add.Tate.transition q n (rootTorsionEquiv q k (n + 1) z) =
      rootTorsionEquiv q k n (ZMod.castHom (pow_dvd_pow q (Nat.le_succ n)) _ z) := by
  obtain ⟨i, rfl⟩ : ∃ i : ℕ, (i : ZMod (q ^ (n + 1))) = z :=
    ⟨z.val, ZMod.natCast_zmod_val z⟩
  apply Subtype.ext
  change (rootTorsionEquiv q k (n + 1) (i : ZMod (q ^ (n + 1)))).val.toMul ^ q =
    (rootTorsionEquiv q k n (ZMod.castHom (pow_dvd_pow q (Nat.le_succ n)) _ (i : ZMod (q ^ (n + 1))))).val.toMul
  rw [map_natCast (ZMod.castHom (pow_dvd_pow q (Nat.le_succ n)) (ZMod (q ^ n))) i]
  unfold rootTorsionEquiv
  rw [primitiveRootTorsionEquiv_natCast, primitiveRootTorsionEquiv_natCast,
    pow_right_comm, compatiblePrimitiveRootUnit_pow]

end

end OAI.AlgebraicGeometry.AbelianScheme.TateComparison.RootTorsionCoordinates

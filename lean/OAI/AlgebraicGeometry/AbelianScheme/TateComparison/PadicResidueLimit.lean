import OAI.AlgebraicGeometry.AbelianScheme.TateComparison.Functor

/-! # Padic Residue Limit -/

namespace OAI.AlgebraicGeometry.AbelianScheme.TateComparison.PadicResidueLimit

noncomputable section

/-! The compatible residue tower is canonically the p-adic integers.
This ring construction will identify the inverse limit of circle torsion. -/

variable (q : ℕ) [Fact q.Prime]

def compatibleResidues : Subring (∀ n : ℕ, ZMod (q ^ n)) where
  carrier := {x | ∀ m n (h : m ≤ n), ZMod.castHom (pow_dvd_pow q h) _ (x n) = x m}
  zero_mem' := by intro m n h; exact map_zero _
  one_mem' := by intro m n h; exact map_one _
  add_mem' hx hy := by intro m n h; exact (map_add _ _ _).trans (congrArg₂ (· + ·) (hx m n h) (hy m n h))
  neg_mem' hx := by intro m n h; exact (map_neg _ _).trans (congrArg Neg.neg (hx m n h))
  mul_mem' hx hy := by intro m n h; exact (map_mul _ _ _).trans (congrArg₂ (· * ·) (hx m n h) (hy m n h))

def residueProjection (n : ℕ) : compatibleResidues q →+* ZMod (q ^ n) :=
  (Pi.evalRingHom _ n).comp (compatibleResidues q).subtype

omit [Fact q.Prime] in
theorem residueProjection_compatible (m n : ℕ) (h : m ≤ n) :
    (ZMod.castHom (pow_dvd_pow q h) _).comp (residueProjection q n) = residueProjection q m := by
  ext x
  exact x.property m n h

def padicResidues : ℤ_[q] →+* compatibleResidues q where
  toFun z := ⟨fun n => PadicInt.toZModPow n z, fun m n h =>
    congrArg (fun f : ℤ_[q] →+* ZMod (q ^ m) => f z)
      (PadicInt.zmod_cast_comp_toZModPow m n h)⟩
  map_zero' := Subtype.ext (funext fun n => (PadicInt.toZModPow n).map_zero)
  map_one' := Subtype.ext (funext fun n => (PadicInt.toZModPow n).map_one)
  map_add' x y := Subtype.ext (funext fun n => (PadicInt.toZModPow n).map_add x y)
  map_mul' x y := Subtype.ext (funext fun n => (PadicInt.toZModPow n).map_mul x y)

def padicResidueLimit : compatibleResidues q →+* ℤ_[q] :=
  PadicInt.lift (residueProjection_compatible q)

theorem padicResidueLimit_spec (x : compatibleResidues q) (n : ℕ) :
    PadicInt.toZModPow n (padicResidueLimit q x) = x.val n :=
  congrArg (fun f : compatibleResidues q →+* ZMod (q ^ n) => f x)
    (PadicInt.lift_spec (residueProjection_compatible q) n)

def padicResidueEquiv : ℤ_[q] ≃+* compatibleResidues q where
  __ := padicResidues q
  invFun := padicResidueLimit q
  left_inv z := PadicInt.ext_of_toZModPow.mp fun n => padicResidueLimit_spec q (padicResidues q z) n
  right_inv x := Subtype.ext (funext fun n => padicResidueLimit_spec q x n)

end

end OAI.AlgebraicGeometry.AbelianScheme.TateComparison.PadicResidueLimit

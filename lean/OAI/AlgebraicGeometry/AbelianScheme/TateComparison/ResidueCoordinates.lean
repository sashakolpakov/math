import OAI.AlgebraicGeometry.AbelianScheme.TateComparison.PadicResidueLimit

/-! # Residue Coordinates -/

namespace OAI.AlgebraicGeometry.AbelianScheme.TateComparison.ResidueCoordinates

noncomputable section

/-! Compatible residue coordinates at the finite torsion levels identify
the actual Tate module with the p-adic integers. -/

variable (q : ℕ) [Fact q.Prime]

omit [Fact q.Prime] in
theorem residues_compatible_of_step (a : ∀ n : ℕ, ZMod (q ^ n))
    (ha : ∀ n, ZMod.castHom (pow_dvd_pow q (Nat.le_succ n)) (ZMod (q ^ n)) (a (n + 1)) = a n)
    (m n : ℕ) (h : m ≤ n) :
    ZMod.castHom (pow_dvd_pow q h) (ZMod (q ^ m)) (a n) = a m := by
  induction n, h using Nat.le_induction with
  | base => rw [ZMod.castHom_self]; rfl
  | succ n hmn ih =>
    have hc := congrArg (fun f : ZMod (q ^ (n + 1)) →+* ZMod (q ^ m) => f (a (n + 1)))
      (ZMod.castHom_comp (pow_dvd_pow q hmn) (pow_dvd_pow q (Nat.le_succ n)))
    change ZMod.castHom (pow_dvd_pow q hmn) (ZMod (q ^ m))
      (ZMod.castHom (pow_dvd_pow q (Nat.le_succ n)) (ZMod (q ^ n)) (a (n + 1))) = _ at hc
    exact hc.symm.trans (by rw [ha, ih])

variable {H : Type*} [AddCommGroup H]
  (e : ∀ n : ℕ, ZMod (q ^ n) ≃+ Add.Tate.torsion q H n)
  (he : ∀ n (z : ZMod (q ^ (n + 1))),
    Add.Tate.transition q n (e (n + 1) z) = e n (ZMod.castHom (pow_dvd_pow q (Nat.le_succ n)) _ z))

def padicToTateCoordinates : ℤ_[q] →ₗ[ℤ_[q]] Add.Tate.Module (H := H) q where
  toFun z := ⟨fun n => e n (PadicInt.toZModPow n z), by
    intro n
    rw [he]
    exact congrArg (e n)
      (congrArg (fun f : ℤ_[q] →+* ZMod (q ^ n) => f z)
        (PadicInt.zmod_cast_comp_toZModPow n (n + 1) (Nat.le_succ n)))⟩
  map_add' x y := by
    apply Subtype.ext
    funext n
    exact (congrArg (e n) ((PadicInt.toZModPow n).map_add x y)).trans ((e n).map_add _ _)
  map_smul' z x := by
    apply Subtype.ext
    funext n
    change e n (PadicInt.toZModPow n (z * x)) = PadicInt.toZModPow n z • e n (PadicInt.toZModPow n x)
    rw [map_mul, ← ZMod.natCast_zmod_val (PadicInt.toZModPow n z),
      ← nsmul_eq_mul, Nat.cast_smul_eq_nsmul, map_nsmul]

def tateCoordinateResidues (x : Add.Tate.Module (H := H) q) : PadicResidueLimit.compatibleResidues q := by
  refine ⟨fun n => (e n).symm (x.val n), residues_compatible_of_step q _ ?_⟩
  intro n
  apply (e n).injective
  rw [← he, AddEquiv.apply_symm_apply, AddEquiv.apply_symm_apply]
  exact x.property n

theorem padicToTateCoordinates_bijective : Function.Bijective (padicToTateCoordinates q e he) := by
  constructor
  · intro x y h
    apply PadicInt.ext_of_toZModPow.mp
    intro n
    exact (e n).injective (congrArg (fun z : Add.Tate.Module (H := H) q => z.val n) h)
  · intro x
    refine ⟨PadicResidueLimit.padicResidueLimit q (tateCoordinateResidues q e he x), ?_⟩
    apply Subtype.ext
    funext n
    change e n (PadicInt.toZModPow n (PadicResidueLimit.padicResidueLimit q (tateCoordinateResidues q e he x))) = x.val n
    rw [PadicResidueLimit.padicResidueLimit_spec]
    exact (e n).apply_symm_apply (x.val n)

def tateEquivOfResidueCoordinates : ℤ_[q] ≃ₗ[ℤ_[q]] Add.Tate.Module (H := H) q :=
  LinearEquiv.ofBijective (padicToTateCoordinates q e he) (padicToTateCoordinates_bijective q e he)

end

end OAI.AlgebraicGeometry.AbelianScheme.TateComparison.ResidueCoordinates

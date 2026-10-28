import OAI.AlgebraicGeometry.PELModuli.CMPoints.BlocksProjectors

/-! # Block Tower -/

namespace OAI.AlgebraicGeometry.PELModuli.CMPoints.BlockTower

noncomputable section

/-! The character blocks form their actual ascending torsion tower.
The image/kernel condition is proved on every test scheme. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj

/-- Transport an actual torsion-kernel condition along group isomorphisms. -/
theorem torsion_kernel_transport
    {G H X Y : Type*} [Group G] [Group H] [Group X] [Group Y]
    (eG : G ≃* X) (eH : H ≃* Y) (i : G →* H) (j : X →* Y) (N : ℕ)
    (hc : ∀ g, eH (i g) = j (eG g))
    (hj : ∀ y, (∃ x, j x = y) ↔ y ^ N = 1) (h : H) :
    (∃ g, i g = h) ↔ h ^ N = 1 := by
  have hp : (eH h) ^ N = 1 ↔ h ^ N = 1 := by
    rw [← map_pow, ← map_one eH, eH.injective.eq_iff]
  refine Iff.trans ?_ ((hj (eH h)).trans hp)
  constructor
  · rintro ⟨g, rfl⟩
    exact ⟨eG g, (hc g).symm⟩
  · rintro ⟨x, hx⟩
    refine ⟨eG.symm x, eH.injective ?_⟩
    exact (hc _).trans ((congrArg j (eG.apply_symm_apply x)).trans hx)

variable {q : ℕ} [Fact q.Prime]

theorem padic_residue_values_modEq (m n : ℕ) (h : m ≤ n) (z : PadicInt q) :
    (PadicInt.toZModPow n z).val ≡ (PadicInt.toZModPow m z).val [MOD q ^ m] := by
  let : NeZero (q ^ m) := ⟨pow_ne_zero _ (Fact.out : q.Prime).ne_zero⟩
  let : NeZero (q ^ n) := ⟨pow_ne_zero _ (Fact.out : q.Prime).ne_zero⟩
  let φ : ZMod (q ^ n) →+* ZMod (q ^ m) := ZMod.castHom (pow_dvd_pow q h) _
  apply (ZMod.natCast_eq_natCast_iff _ _ _).mp
  calc
    ((PadicInt.toZModPow n z).val : ZMod (q ^ m)) =
        φ ((PadicInt.toZModPow n z).val : ZMod (q ^ n)) := (map_natCast φ _).symm
    _ = φ (PadicInt.toZModPow n z) := congrArg φ (ZMod.natCast_zmod_val _)
    _ = PadicInt.toZModPow m z :=
      RingHom.congr_fun (PadicInt.zmod_cast_comp_toZModPow m n h) z
    _ = ((PadicInt.toZModPow m z).val : ZMod (q ^ m)) :=
      (ZMod.natCast_zmod_val _).symm

variable {O : Type} [CommRing O] {S : Scheme} {g : ℕ}
  (A : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g S) (ρ : AbelianModuli.ReferenceFamily.ActionData.IntegralAction O A)
  (χ : O →+* PadicInt q)

/-- Equality with the lower-level kernel, including infinitesimal points. -/
theorem block_membership_lower_iff (m n : ℕ) (h : m ≤ n)
    (T : Over S) (x : T ⟶ A.scheme) :
    x ∈ BlocksProjectors.blockPoints A ρ χ m T ↔ x ∈ BlocksProjectors.blockPoints A ρ χ n T ∧ x ^ (q ^ m) = 1 := by
  constructor
  · intro hx
    refine ⟨⟨?_, ?_⟩, hx.1⟩
    · obtain ⟨r, hr⟩ := pow_dvd_pow q h
      rw [hr, pow_mul, hx.1, one_pow]
    · intro a
      exact (hx.2 a).trans
        (pow_eq_pow_of_modEq (padic_residue_values_modEq m n h (χ a)).symm hx.1)
  · rintro ⟨hx, hxm⟩
    exact ⟨hxm, fun a => (hx.2 a).trans
      (pow_eq_pow_of_modEq (padic_residue_values_modEq m n h (χ a)) hxm)⟩

theorem blockPoints_mono (m n : ℕ) (h : m ≤ n) (T : Over S) :
    BlocksProjectors.blockPoints A ρ χ m T ≤ BlocksProjectors.blockPoints A ρ χ n T :=
  fun x hx => ((block_membership_lower_iff A ρ χ m n h T x).mp hx).1

def blockLevelInclusion (m n : ℕ) (h : m ≤ n) (T : Over S) :
    BlocksProjectors.blockPoints A ρ χ m T →* BlocksProjectors.blockPoints A ρ χ n T :=
  Subgroup.inclusion (blockPoints_mono A ρ χ m n h T)

theorem blockLevelInclusion_kernel (m n : ℕ) (h : m ≤ n) (T : Over S)
    (x : BlocksProjectors.blockPoints A ρ χ n T) :
    (∃ y, blockLevelInclusion A ρ χ m n h T y = x) ↔ x ^ (q ^ m) = 1 := by
  constructor
  · rintro ⟨y, rfl⟩
    apply Subtype.ext
    exact y.property.1
  · intro hx
    have hx' : x.val ^ (q ^ m) = 1 := congrArg Subtype.val hx
    refine ⟨⟨x.val, (block_membership_lower_iff A ρ χ m n h T x.val).mpr
      ⟨x.property, hx'⟩⟩, ?_⟩
    rfl

def blockInclusionNat (m n : ℕ) (h : m ≤ n) :
    BlocksProjectors.blockFunctor A ρ χ m ⟶ BlocksProjectors.blockFunctor A ρ χ n where
  app T := GrpCat.ofHom (blockLevelInclusion A ρ χ m n h T.unop)
  naturality _ _ _ := rfl

theorem blockInclusionNat_injective (m n : ℕ) (h : m ≤ n) (T : Over S) :
    Function.Injective ((blockInclusionNat A ρ χ m n h).app (.op T)) := by
  intro x y hxy
  exact Subtype.ext (congrArg (fun z : BlocksProjectors.blockPoints A ρ χ n T => z.val) hxy)

end

end OAI.AlgebraicGeometry.PELModuli.CMPoints.BlockTower

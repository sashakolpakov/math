import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Datum

/-! # Groups -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Groups

noncomputable section

/-! Actual unitary, special-unitary, and principal lattice subgroups. -/

variable {R V W : Type*} [CommRing R] [AddCommGroup V] [Module R V]

def unitarySubgroup (h : V → V → W) : Subgroup (V ≃ₗ[R] V) where
  carrier := {g | ∀ x y, h (g x) (g y) = h x y}
  one_mem' := fun _ _ => rfl
  mul_mem' hg hk := fun x y => (hg _ _).trans (hk x y)
  inv_mem' := by
    intro g hg x y
    change h (g.symm x) (g.symm y) = h x y
    have hxy := hg (g.symm x) (g.symm y)
    simpa only [LinearEquiv.apply_symm_apply] using hxy.symm

def specialUnitarySubgroup (h : V → V → W) : Subgroup (V ≃ₗ[R] V) :=
  unitarySubgroup h ⊓ (LinearEquiv.det : (V ≃ₗ[R] V) →* Rˣ).ker

def principalLatticeSubgroup (Λ : AddSubgroup V) (N : ℕ) :
    Subgroup (V ≃ₗ[R] V) where
  carrier := {g | (∀ x, x ∈ Λ ↔ g x ∈ Λ) ∧
    ∀ x ∈ Λ, ∃ y ∈ Λ, g x - x = N • y}
  one_mem' := by
    refine ⟨fun _ => Iff.rfl, ?_⟩
    intro x _
    exact ⟨0, Λ.zero_mem, by simp⟩
  mul_mem' := by
    rintro g k ⟨hg, hgc⟩ ⟨hk, hkc⟩
    refine ⟨fun x => (hk x).trans (hg (k x)), ?_⟩
    intro x hx
    obtain ⟨y, hy, hgy⟩ := hgc (k x) ((hk x).mp hx)
    obtain ⟨z, hz, hkz⟩ := hkc x hx
    refine ⟨y + z, Λ.add_mem hy hz, ?_⟩
    change g (k x) - x = N • (y + z)
    rw [smul_add, ← hgy, ← hkz]
    abel
  inv_mem' := by
    rintro g ⟨hg, hgc⟩
    have hi (x : V) : x ∈ Λ ↔ g.symm x ∈ Λ := by
      simpa only [LinearEquiv.apply_symm_apply] using (hg (g.symm x)).symm
    refine ⟨hi, ?_⟩
    intro x hx
    obtain ⟨y, hy, hgy⟩ := hgc (g.symm x) ((hi x).mp hx)
    refine ⟨-y, Λ.neg_mem hy, ?_⟩
    change g.symm x - x = N • -y
    rw [smul_neg, ← hgy, LinearEquiv.apply_symm_apply]
    abel

variable {E : Type*} [Field E] [NumberField E] [Algebra ℚ E]
  [NumberField.IsCMField E]

def principalSpecialUnitary (b : E) (Λ : Submodule ℤ (NumberTheory.ArithmeticGroups.Data.CongruenceLevel.VE E)) (N : ℕ) :
    Subgroup (NumberTheory.ArithmeticGroups.Data.CongruenceLevel.VE E ≃ₗ[E] NumberTheory.ArithmeticGroups.Data.CongruenceLevel.VE E) :=
  principalLatticeSubgroup Λ.toAddSubgroup N ⊓ specialUnitarySubgroup (NumberTheory.ArithmeticGroups.Data.CongruenceLevel.hermitian b)

omit [Algebra ℚ E] in
theorem mem_principalSpecialUnitary (b : E) (Λ : Submodule ℤ (NumberTheory.ArithmeticGroups.Data.CongruenceLevel.VE E)) (N : ℕ)
    (g : NumberTheory.ArithmeticGroups.Data.CongruenceLevel.VE E ≃ₗ[E] NumberTheory.ArithmeticGroups.Data.CongruenceLevel.VE E) :
    g ∈ principalSpecialUnitary b Λ N ↔
      NumberTheory.ArithmeticGroups.Data.CongruenceLevel.PrincipalLevel b Λ N g ∧ LinearMap.det g.toLinearMap = 1 := by
  change ((_ ∧ _) ∧ _ ∧ LinearEquiv.det g = 1) ↔ _
  have hd : LinearEquiv.det g = 1 ↔ LinearMap.det g.toLinearMap = 1 := by
    rw [← Units.val_inj]
    simp only [LinearEquiv.coe_det, Units.val_one]
  rw [hd]
  simp only [NumberTheory.ArithmeticGroups.Data.CongruenceLevel.PrincipalLevel, natCast_zsmul]
  tauto

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Groups

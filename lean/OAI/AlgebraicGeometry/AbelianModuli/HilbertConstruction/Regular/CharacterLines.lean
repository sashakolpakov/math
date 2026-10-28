import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.CharacterAlgebraBasis

/-! # Character Lines -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Regular.CharacterLines

noncomputable section

/-! Each character eigenspace of the regular function representation is canonically a free module of rank one over every coefficient algebra. -/
universe u v w
variable (K : Type u) [Field K] (G : Type v) [CommGroup G]
    (R : Type w) [CommRing R] [Algebra K R]

def regularCharacterLine (χ : G →* Kˣ) : Submodule R (G → R) where
  carrier := {v | ∀ a b : G, v (b * a) = algebraMap K R (χ a : K) * v b}
  zero_mem' := by intro a b; simp
  add_mem' := by
    intro v w hv hw a b
    exact (congrArg₂ (fun x y : R => x + y) (hv a b) (hw a b)).trans (mul_add _ _ _).symm
  smul_mem' := by
    intro r v hv a b
    change r * v (b * a) = algebraMap K R (χ a : K) * (r * v b)
    rw [hv a b, mul_left_comm]

def regularCharacterLineEquiv (χ : G →* Kˣ) : regularCharacterLine K G R χ ≃ₗ[R] R where
  toFun v := v.val 1
  invFun r := ⟨fun g => algebraMap K R (χ g : K) * r, by
    intro a b
    simp only [map_mul, Units.val_mul]
    ring⟩
  left_inv v := by
    apply Subtype.ext
    funext g
    exact (v.property g 1).symm.trans (congrArg v.val (one_mul g))
  right_inv r := by simp
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

@[simp]
theorem regularCharacterLineEquiv_apply (χ : G →* Kˣ) (v : regularCharacterLine K G R χ) :
    regularCharacterLineEquiv K G R χ v = v.val 1 := rfl

@[simp]
theorem regularCharacterLineEquiv_symm_apply (χ : G →* Kˣ) (r : R) (g : G) :
    ((regularCharacterLineEquiv K G R χ).symm r).val g = algebraMap K R (χ g : K) * r := rfl

theorem regularCharacterLine_finite_free (χ : G →* Kˣ) :
    Module.Finite R (regularCharacterLine K G R χ) ∧ Module.Free R (regularCharacterLine K G R χ) :=
  ⟨Module.Finite.equiv (regularCharacterLineEquiv K G R χ).symm,
    Module.Free.of_equiv (regularCharacterLineEquiv K G R χ).symm⟩

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Regular.CharacterLines

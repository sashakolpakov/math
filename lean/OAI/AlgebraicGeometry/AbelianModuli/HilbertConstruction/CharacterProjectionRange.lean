import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Regular.CharacterProjectors

/-! # Character Projection Range -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.CharacterProjectionRange

noncomputable section

/-! The range of each regular character projector is exactly its explicit rank-one character line. -/
universe u v w
variable (K : Type u) [Field K] (G : Type v) [CommGroup G] [Fintype G]
    [HasEnoughRootsOfUnity K (Monoid.exponent G)]
    (R : Type w) [CommRing R] [Algebra K R]

theorem regularCharacterLine_eq_smul_basis (χ : G →* Kˣ) (v : Regular.CharacterLines.regularCharacterLine K G R χ) :
    v.val = v.val 1 • CharacterAlgebraBasis.finiteAbelianCharacterAlgebraBasis K G R χ := by
  funext g
  have h : v.val g = algebraMap K R (χ g : K) * v.val 1 := by
    simpa only [one_mul] using v.property g 1
  exact h.trans (by simp only [Pi.smul_apply, smul_eq_mul, CharacterAlgebraBasis.finiteAbelianCharacterAlgebraBasis_apply, mul_comm])

theorem regularCharacterProjector_fixed (χ : G →* Kˣ) (v : Regular.CharacterLines.regularCharacterLine K G R χ) :
    Regular.CharacterProjectors.regularCharacterProjector K G R χ v.val = v.val := by
  classical
  rw [regularCharacterLine_eq_smul_basis K G R χ v, map_smul]
  simp only [Regular.CharacterProjectors.regularCharacterProjector_basis, ite_true]

theorem regularCharacterProjector_range (χ : G →* Kˣ) :
    (Regular.CharacterProjectors.regularCharacterProjector K G R χ).range = Regular.CharacterLines.regularCharacterLine K G R χ := by
  apply le_antisymm
  · rintro _ ⟨v, rfl⟩
    exact (Regular.CharacterProjectors.regularCharacterComponent K G R χ v).property
  · intro v hv
    exact ⟨v, regularCharacterProjector_fixed K G R χ ⟨v, hv⟩⟩

def regularCharacterProjectorRangeEquiv (χ : G →* Kˣ) :
    (Regular.CharacterProjectors.regularCharacterProjector K G R χ).range ≃ₗ[R] R :=
  LinearEquiv.ofEq _ _ (regularCharacterProjector_range K G R χ) ≪≫ₗ Regular.CharacterLines.regularCharacterLineEquiv K G R χ

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.CharacterProjectionRange

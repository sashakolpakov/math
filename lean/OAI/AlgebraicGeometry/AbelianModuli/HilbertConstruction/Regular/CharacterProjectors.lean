import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Regular.CharacterLines

/-! # Character Projectors -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Regular.CharacterProjectors

noncomputable section

/-! The character basis gives explicit rank-one component maps and mutually orthogonal projections summing to the identity on regular functions. -/
universe u v w
variable (K : Type u) [Field K] (G : Type v) [CommGroup G] [Fintype G]
    [HasEnoughRootsOfUnity K (Monoid.exponent G)]
    (R : Type w) [CommRing R] [Algebra K R]

def regularCharacterComponent (χ : G →* Kˣ) : (G → R) →ₗ[R] CharacterLines.regularCharacterLine K G R χ :=
  (CharacterLines.regularCharacterLineEquiv K G R χ).symm.toLinearMap.comp
    ((CharacterAlgebraBasis.finiteAbelianCharacterAlgebraBasis K G R).coord χ)

def regularCharacterProjector (χ : G →* Kˣ) : (G → R) →ₗ[R] (G → R) :=
  (CharacterLines.regularCharacterLine K G R χ).subtype.comp (regularCharacterComponent K G R χ)

@[simp]
theorem regularCharacterProjector_apply (χ : G →* Kˣ) (v : G → R) (g : G) :
    regularCharacterProjector K G R χ v g =
      algebraMap K R (χ g : K) * (CharacterAlgebraBasis.finiteAbelianCharacterAlgebraBasis K G R).repr v χ := rfl

theorem regularCharacterProjector_eq_smulBasis (χ : G →* Kˣ) (v : G → R) :
    regularCharacterProjector K G R χ v =
      (CharacterAlgebraBasis.finiteAbelianCharacterAlgebraBasis K G R).repr v χ • CharacterAlgebraBasis.finiteAbelianCharacterAlgebraBasis K G R χ := by
  funext g
  simp only [regularCharacterProjector_apply, Pi.smul_apply, smul_eq_mul,
    CharacterAlgebraBasis.finiteAbelianCharacterAlgebraBasis_apply, mul_comm]

@[simp]
theorem regularCharacterProjector_basis [DecidableEq (G →* Kˣ)] (χ ψ : G →* Kˣ) :
    regularCharacterProjector K G R χ (CharacterAlgebraBasis.finiteAbelianCharacterAlgebraBasis K G R ψ) =
      if ψ = χ then CharacterAlgebraBasis.finiteAbelianCharacterAlgebraBasis K G R ψ else 0 := by
  classical
  rw [regularCharacterProjector_eq_smulBasis, Module.Basis.repr_self_apply]
  split_ifs with h
  · subst ψ; exact one_smul _ _
  · exact zero_smul _ _

theorem regularCharacterProjector_idempotent (χ : G →* Kˣ) :
    (regularCharacterProjector K G R χ).comp (regularCharacterProjector K G R χ) =
      regularCharacterProjector K G R χ := by
  classical
  apply (CharacterAlgebraBasis.finiteAbelianCharacterAlgebraBasis K G R).ext
  intro ψ
  by_cases h : ψ = χ
  · simp only [LinearMap.comp_apply, regularCharacterProjector_basis, ite_eq_left h]
  · simp only [LinearMap.comp_apply, regularCharacterProjector_basis, ite_eq_right h, map_zero]

theorem regularCharacterProjector_orthogonal (χ ψ : G →* Kˣ) (h : ψ ≠ χ) :
    (regularCharacterProjector K G R χ).comp (regularCharacterProjector K G R ψ) = 0 := by
  classical
  apply (CharacterAlgebraBasis.finiteAbelianCharacterAlgebraBasis K G R).ext
  intro η
  by_cases hη : η = ψ
  · subst η
    simp [regularCharacterProjector_basis, h]
  · simp only [LinearMap.comp_apply, regularCharacterProjector_basis, ite_eq_right hη, map_zero, LinearMap.zero_apply]

theorem regularCharacterProjector_sum [Fintype (G →* Kˣ)] :
    ∑ χ : G →* Kˣ, regularCharacterProjector K G R χ = LinearMap.id := by
  apply LinearMap.ext
  intro v
  simp only [LinearMap.sum_apply, regularCharacterProjector_eq_smulBasis, LinearMap.id_apply,
    Module.Basis.sum_repr]

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Regular.CharacterProjectors

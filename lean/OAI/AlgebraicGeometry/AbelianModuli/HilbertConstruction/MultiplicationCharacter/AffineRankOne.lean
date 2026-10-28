import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Affine.RestrictedPullbackBasis
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.MultiplicationCharacter.PullbackLineBundles
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.MultiplicationCharacter.Quasicoherence
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.LevelMultiplication.Surjectivity
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.FlatRankOneDescent

/-! # Affine Rank One -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction

noncomputable section

/-! The actual character comparison gives rank-one scalar-extended sections. Faithfully flat descent proves the original character-section modules finite, flat and everywhere of rank one. -/
open _root_.CategoryTheory _root_.AlgebraicGeometry
universe u
variable {K : Type u} [Field K] [IsAlgClosed K] {g N : ℕ} [NeZero N]
    (A : Abelian.Schemes.AbelianScheme g (Spec (.of K))) (level : A.FullLevel N)

theorem Abelian.Schemes.AbelianScheme.multiplicationCharacter_affine_rankOne
    (χ : ULift.{u} (Multiplicative (Fin (2 * g) → ZMod N)) →* Kˣ) (hN : (N : K) ≠ 0)
    (U : A.scheme.left.Opens) (hU : IsAffineOpen U) :
    Module.Finite Γ(U.toScheme, ⊤) Γ((A.multiplicationCharacterSheaf level χ).restrict U.ι, ⊤) ∧
    Module.Flat Γ(U.toScheme, ⊤) Γ((A.multiplicationCharacterSheaf level χ).restrict U.ι, ⊤) ∧
    ∀ p : PrimeSpectrum Γ(U.toScheme, ⊤),
      Module.rankAtStalk Γ((A.multiplicationCharacterSheaf level χ).restrict U.ι, ⊤) p = 1 := by
  let f := (A.multiplication N).left
  let G := ULift.{u} (Multiplicative (Fin (2 * g) → ZMod N))
  let c := Coefficient.ModulePresheaf.schemeCoefficientMap A.scheme.hom
  have := A.fullLevel_multiplication_isFinite level
  have := A.fullLevel_multiplication_etale level
  have := A.fullLevel_multiplication_surjective level
  have : IsAffine U.toScheme := hU
  have : IsAffine (f ⁻¹ᵁ U).toScheme := hU.preimage f
  have := A.multiplicationCharacterSheaf_quasicoherent level χ
  have : Surjective (f ∣_ U) :=
    MorphismProperty.IsStableUnderBaseChange.of_isPullback (P := @Surjective)
      (isPullback_morphismRestrict f U).flip (A.fullLevel_multiplication_surjective level)
  let : Algebra Γ(U.toScheme, ⊤) Γ((f ⁻¹ᵁ U).toScheme, ⊤) :=
    (f ∣_ U).appTop.hom.toAlgebra
  have hfaithful : (f ∣_ U).appTop.hom.FaithfullyFlat :=
    (Flat.flat_and_surjective_iff_faithfullyFlat_of_isAffine (f ∣_ U)).mp
      ⟨inferInstance, inferInstance⟩
  have : Module.FaithfullyFlat Γ(U.toScheme, ⊤) Γ((f ⁻¹ᵁ U).toScheme, ⊤) := hfaithful
  have hG := TameCharacters.fullLevelCharacter_order_nonzero K g N hN
  have := TameCharacters.tameFiniteAbelian_hasEnoughRoots K G hG
  let e := Affine.RestrictedPullbackBasis.affineRestrictedPullbackBasis f U (A.multiplicationCharacterSheaf level χ)
    (Constant.CharacterSheafSections.constantCharacterSheaf c G χ) (A.multiplicationCharacterComparisonIso level χ hN)
    (Constant.CharacterSheafSections.constantCharacterSheafSectionsEquiv c G χ hG (f ⁻¹ᵁ U))
  exact FlatRankOneDescent.faithfullyFlat_rankOne_descent e

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction

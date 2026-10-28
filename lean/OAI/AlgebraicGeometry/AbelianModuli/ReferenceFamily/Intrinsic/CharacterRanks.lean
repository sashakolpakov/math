import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Polarized.TangentEquiv
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.Lie

/-! # Character Ranks -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.CharacterRanks

noncomputable section

/-! The original structure-sheaf H1 character space has the conjugate
native Lie rank, through the constructed polarization and Picard tangent
equivalence and the actual Rosati identity. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

local instance nativeH1CharacterIntegral {n : ℕ} (G : HilbertConstruction.Abelian.Schemes.AbelianScheme n Foundations.Scheme.ProjectiveSpace.complexBase) :
    IsIntegral G.scheme.left := Abelian.IntrinsicAdapter.AbelianIntrinsicAdapter.carrier_integral G

local instance nativeH1CharacterModule (G : Over Foundations.Scheme.ProjectiveSpace.complexBase) : Module ℂ (SheafCohomology.AffineH.Projective.H (HilbertConstruction.Line.Bundles.structureModule G.left) 1) :=
  StructureComplexScalars.structureH1ComplexModule G

def nativeStructureH1Eigenspace {R : Type} [CommRing R] {g : ℕ}
    (A : HilbertConstruction.Abelian.Schemes.AbelianScheme g Foundations.Scheme.ProjectiveSpace.complexBase) (ρ : ActionData.IntegralAction R A) (τ : R →+* ℂ) :
    Submodule ℂ (SheafCohomology.AffineH.Projective.H (HilbertConstruction.Line.Bundles.structureModule A.scheme.left) 1) where
  carrier := {x | ∀ a, StructurePullbackLinear.nativeStructureH1PullbackLinear (ρ.map a) x = τ a • x}
  zero_mem' a := by rw [map_zero, smul_zero]
  add_mem' hx hy a := by rw [map_add, hx a, hy a, smul_add]
  smul_mem' c x hx a := by rw [map_smul, hx a, smul_comm]

variable {E : Type} [Field E] [NumberField E] [NumberField.IsCMField E]

theorem integralCMConjugation_involutive (a : NumberField.RingOfIntegers E) :
    NumberField.IsCMField.ringOfIntegersComplexConj E
      (NumberField.IsCMField.ringOfIntegersComplexConj E a) = a :=
  NumberField.RingOfIntegers.ext (NumberField.IsCMField.complexConj_apply_apply E (a : E))

variable {g N : ℕ} {δ : Fin g → ℕ}
    (A : HilbertConstruction.PolarizationData.PolarizedAbelianWithFullLevel g δ N Foundations.Scheme.ProjectiveSpace.complexBase)
    (ρ : ActionData.IntegralAction (NumberField.RingOfIntegers E) A.abelian) (hρ : ActionData.RosatiConjugation A ρ)
    (τ : NumberField.RingOfIntegers E →+* ℂ)

include hρ

theorem polarizedStructureH1Tangent_eigen_iff
    (v : Fin (Betti.AffineDimension.Realization.functionFieldDifferentialDimension A.abelian.scheme.hom) → ℂ) :
    Polarized.TangentEquiv.polarizedStructureH1TangentEquiv A v ∈ nativeStructureH1Eigenspace A.abelian ρ τ ↔
      v ∈ Lie.nativeLieEigenspace A.abelian ρ
        (τ.comp (NumberField.IsCMField.ringOfIntegersComplexConj E).toRingHom) := by
  constructor
  · intro hv a
    apply (Polarized.TangentEquiv.polarizedStructureH1TangentEquiv A).injective
    have hc := Polarized.TangentAction.polarizedStructureH1TangentLinear_rosati A ρ hρ
      (NumberField.IsCMField.ringOfIntegersComplexConj E a) v
    rw [integralCMConjugation_involutive] at hc
    exact hc.trans ((hv (NumberField.IsCMField.ringOfIntegersComplexConj E a)).trans
      ((Polarized.TangentEquiv.polarizedStructureH1TangentEquiv A).map_smul (τ (NumberField.IsCMField.ringOfIntegersComplexConj E a)) v).symm)
  · intro hv a
    have h := hv (NumberField.IsCMField.ringOfIntegersComplexConj E a)
    change Lie.nativeLieDifferential A.abelian ρ (NumberField.IsCMField.ringOfIntegersComplexConj E a) v =
      τ (NumberField.IsCMField.ringOfIntegersComplexConj E
        (NumberField.IsCMField.ringOfIntegersComplexConj E a)) • v at h
    rw [integralCMConjugation_involutive] at h
    exact (Polarized.TangentAction.polarizedStructureH1TangentLinear_rosati A ρ hρ a v).symm.trans
      ((congrArg (Polarized.TangentEquiv.polarizedStructureH1TangentEquiv A) h).trans
        ((Polarized.TangentEquiv.polarizedStructureH1TangentEquiv A).map_smul (τ a) v))

def polarizedNativeH1CharacterEquiv :
    Lie.nativeLieEigenspace A.abelian ρ (τ.comp (NumberField.IsCMField.ringOfIntegersComplexConj E).toRingHom) ≃ₗ[ℂ]
      nativeStructureH1Eigenspace A.abelian ρ τ where
  toFun v := ⟨Polarized.TangentEquiv.polarizedStructureH1TangentEquiv A v.val,
    (polarizedStructureH1Tangent_eigen_iff A ρ hρ τ v.val).mpr v.property⟩
  invFun x := ⟨(Polarized.TangentEquiv.polarizedStructureH1TangentEquiv A).symm x.val, by
    apply (polarizedStructureH1Tangent_eigen_iff A ρ hρ τ _).mp
    rw [LinearEquiv.apply_symm_apply]
    exact x.property⟩
  left_inv v := Subtype.ext ((Polarized.TangentEquiv.polarizedStructureH1TangentEquiv A).symm_apply_apply v.val)
  right_inv x := Subtype.ext ((Polarized.TangentEquiv.polarizedStructureH1TangentEquiv A).apply_symm_apply x.val)
  map_add' v w := Subtype.ext ((Polarized.TangentEquiv.polarizedStructureH1TangentEquiv A).map_add v.val w.val)
  map_smul' c v := Subtype.ext ((Polarized.TangentEquiv.polarizedStructureH1TangentEquiv A).map_smul c v.val)

theorem nativeStructureH1Eigenspace_finrank_of_lieRank {r : ℕ}
    (hr : LieRanks.HasLieRank A.abelian ρ
      (τ.comp (NumberField.IsCMField.ringOfIntegersComplexConj E).toRingHom) r) :
    Module.finrank ℂ (nativeStructureH1Eigenspace A.abelian ρ τ) = r :=
  (polarizedNativeH1CharacterEquiv A ρ hρ τ).finrank_eq.symm.trans
    (hr.native_finrank A.abelian ρ _)

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.CharacterRanks

import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.PolarizedFamilyTangentSymmetry
import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.PELCharacterConjugation
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.SupportedBilinearDimension

/-! # Polarized PEL Family Tangent -/

namespace OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.PolarizedPELFamilyTangent.Construction

noncomputable section

/-! The actual tangent map of a polarized CM family with the original
PEL Lie ranks takes values in the original distinguished two-by-one
coefficient space. Both symmetry and character support are proved. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj

open OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.SupportedBilinearDimension

attribute [local implicit_reducible] AbelianModuli.ReferenceFamily.TangentBasePoint.fixedFamilyFiber AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme.pullback
attribute [local instance] AbelianModuli.ReferenceFamily.Abelian.Tangent.abelianFamilyFixedFiber_smooth AbelianModuli.ReferenceFamily.Abelian.Tangent.abelianFamilyFixedFiber_proper
  AbelianModuli.ReferenceFamily.Abelian.Tangent.abelianFamilyFixedFiber_connected AbelianModuli.ReferenceFamily.Abelian.Tangent.abelianFamilyFixedFiber_integral AbelianModuli.ReferenceFamily.FamilyTangent.IntrinsicVanishing.familyNativeFixedFiber_group

variable {E : Type} [Field E] [NumberField E] [Algebra ℚ E] [NumberField.IsCMField E]
    {s N : ℕ} (P : AbelianModuli.ReferenceFamily.Datum.RankThreePELDatum E s) (hP : P.IsAdmissible)
    (R : Type) [CommRing R] [Algebra ℂ R] [Algebra R ℂ] [IsScalarTower ℂ R ℂ]
    (A : AbelianModuli.HilbertConstruction.PolarizationData.PolarizedAbelianWithFullLevel (3 * s) P.polarizationType N (Spec (.of R)))
    (ρ : AbelianModuli.ReferenceFamily.ActionData.IntegralAction (NumberField.RingOfIntegers E) A.abelian) (hρ : AbelianModuli.ReferenceFamily.ActionData.RosatiConjugation A ρ)
    (U : A.abelian.scheme.left.AffineOpenCover)
    (hr : ∀ j, AbelianModuli.ReferenceFamily.LieRanks.HasLieRank
      (A.abelian.pullback (Spec.map (CommRingCat.ofHom (algebraMap R ℂ))))
      (ρ.pullback (Spec.map (CommRingCat.ofHom (algebraMap R ℂ))))
      (AbelianModuli.ReferenceFamily.PEL.ConormalCharacterBasis.pairedIntegralCharacter P j) (P.pairedLieRank j))

def polarizedPELFamilyConormalBasis :=
  AbelianModuli.ReferenceFamily.PEL.ConormalCharacterBasis.pelConormalCharacterBasis P
    (A.abelian.pullback (Spec.map (CommRingCat.ofHom (algebraMap R ℂ))))
    (ρ.pullback (Spec.map (CommRingCat.ofHom (algebraMap R ℂ)))) hP hr

def polarizedPELFamilyForms :=
  AbelianModuli.ReferenceFamily.SupportedBilinearDimension.basisCrossSymmetricForms (polarizedPELFamilyConormalBasis P hP R A ρ hr)
    (PELCharacterSupportIndices.Construction.pelPositiveTangentIndices P) (PELCharacterSupportIndices.Construction.pelNegativeTangentIndices P)

def polarizedPELFamilyTangent : Derivation ℂ R ℂ →ₗ[ℂ]
    polarizedPELFamilyForms P hP R A ρ hr :=
  (AbelianModuli.ReferenceFamily.Polarized.TangentBilinear.polarizedFamilyTangentBilinear R A U).codRestrict _ (by
    intro d
    constructor
    · intro i j
      exact PolarizedFamilyTangentSymmetry.Construction.polarizedFamilyTangentBilinear_symmetric R A U d _ _
    · intro i j hn
      exact PELCharacterConjugation.Construction.pelBalancedBilinear_characterSupport P
        (A.abelian.pullback (Spec.map (CommRingCat.ofHom (algebraMap R ℂ))))
        (ρ.pullback (Spec.map (CommRingCat.ofHom (algebraMap R ℂ)))) hP hr
        (AbelianModuli.ReferenceFamily.Polarized.TangentBilinear.polarizedFamilyTangentBilinear R A U d)
        (fun a z w => AbelianModuli.ReferenceFamily.Polarized.TangentBilinear.polarizedFamilyTangentBilinear_balanced R A U ρ hρ a d z w) i j hn)

omit [Algebra ℂ R] [IsScalarTower ℂ R ℂ] in
theorem polarizedPELFamilyForms_finrank_le_two :
    Module.finrank ℂ (polarizedPELFamilyForms P hP R A ρ hr) ≤ 2 :=
  AbelianModuli.ReferenceFamily.SupportedBilinearDimension.basisCrossSymmetricForms_finrank_le_two (polarizedPELFamilyConormalBasis P hP R A ρ hr)
    (PELCharacterSupportIndices.Construction.pelPositiveTangentIndices P) (PELCharacterSupportIndices.Construction.pelNegativeTangentIndices P)
    (PELCharacterSupportIndices.Construction.pelPositiveTangentIndices_card P) (PELCharacterSupportIndices.Construction.pelNegativeTangentIndices_card P)

theorem polarizedPELFamilyTangent_eq_iff (d e : Derivation ℂ R ℂ) :
    polarizedPELFamilyTangent P hP R A ρ hρ U hr d =
      polarizedPELFamilyTangent P hP R A ρ hρ U hr e ↔
      AbelianModuli.ReferenceFamily.Family.BaseTangentObstruction.familyBaseTangentObstruction R A.abelian.scheme U d =
        AbelianModuli.ReferenceFamily.Family.BaseTangentObstruction.familyBaseTangentObstruction R A.abelian.scheme U e := by
  constructor
  · intro h
    exact (AbelianModuli.ReferenceFamily.Polarized.TangentBilinear.polarizedFamilyTangentBilinear_eq_iff R A U d e).mp (congrArg Subtype.val h)
  · intro h
    apply Subtype.ext
    exact (AbelianModuli.ReferenceFamily.Polarized.TangentBilinear.polarizedFamilyTangentBilinear_eq_iff R A U d e).mpr h

end

end OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.PolarizedPELFamilyTangent.Construction

import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.PolarizedPELFamilyTangent
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.PELAffineTangentInjection

/-! # Fine PEL Tangent Dimension -/

namespace OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.FinePELTangentDimension.Construction

noncomputable section

/-! Every monic affine chart of the original fine PEL complex fiber
has tangent dimension at most two. The Lie ranks are obtained from its
actual universal PEL object, and the tangent injection and symmetric
coefficient-space bound are the original constructed maps. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj

attribute [local implicit_reducible] AbelianModuli.ReferenceFamily.EtaleSplittingAt.EtaleSplitting.affineOver AbelianModuli.ReferenceFamily.TangentBasePoint.fixedFamilyFiber AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme.pullback
attribute [local instance] AbelianModuli.ReferenceFamily.Abelian.Tangent.abelianFamilyFixedFiber_smooth AbelianModuli.ReferenceFamily.Abelian.Tangent.abelianFamilyFixedFiber_proper
  AbelianModuli.ReferenceFamily.Abelian.Tangent.abelianFamilyFixedFiber_connected AbelianModuli.ReferenceFamily.Abelian.Tangent.abelianFamilyFixedFiber_integral AbelianModuli.ReferenceFamily.FamilyTangent.IntrinsicVanishing.familyNativeFixedFiber_group

namespace FinePELModel

variable {E K : Type} [Field E] [NumberField E]
    [NumberField.IsCMField E] [IsGalois ℚ E] [Field K]
    {s N : ℕ} [NeZero N] {P : AbelianModuli.ReferenceFamily.Datum.RankThreePELDatum E s} {iota : E →+* K}
    (M : AbelianModuli.ReferenceFamily.Models.FinePELModel P iota N) (hP : P.IsAdmissible) (hM : M.IsFine)
    (κ : K →+* ℂ) (hκ : κ.comp iota = P.μ)
    (R : Type) [CommRing R] [Algebra ℂ R] [Algebra R ℂ] [IsScalarTower ℂ R ℂ]
    (f : AbelianModuli.ReferenceFamily.EtaleSplittingAt.EtaleSplitting.affineOver ℂ R ⟶ M.complexFiber κ) [Mono f]

include hP hκ in
omit [NeZero N] [Mono f] in
theorem affineUniversalFixedFiber_pairedRank (j : Fin s × Bool) :
    AbelianModuli.ReferenceFamily.LieRanks.HasLieRank
      ((M.complexTestFamily κ f).polarized.abelian.pullback
        (Spec.map (CommRingCat.ofHom (algebraMap R ℂ))))
      ((M.complexTestFamily κ f).action.pullback
        (Spec.map (CommRingCat.ofHom (algebraMap R ℂ))))
      (AbelianModuli.ReferenceFamily.PEL.ConormalCharacterBasis.pairedIntegralCharacter P j) (P.pairedLieRank j) := by
  let p := Spec.map (CommRingCat.ofHom (algebraMap R ℂ))
  have hc : CommRingCat.ofHom (algebraMap ℂ R) ≫ CommRingCat.ofHom (algebraMap R ℂ) =
      𝟙 (CommRingCat.of ℂ) := by
    ext c
    change algebraMap R ℂ (algebraMap ℂ R c) = c
    simpa using (IsScalarTower.algebraMap_apply ℂ R ℂ c).symm
  have hp : p ≫ (AbelianModuli.ReferenceFamily.Complex.BallPeriods.restrictComplexBase κ (AbelianModuli.ReferenceFamily.EtaleSplittingAt.EtaleSplitting.affineOver ℂ R)).hom =
      Spec.map (CommRingCat.ofHom κ) := by
    change p ≫ (Spec.map (CommRingCat.ofHom (algebraMap ℂ R)) ≫
      Spec.map (CommRingCat.ofHom κ)) = _
    rw [← Category.assoc, ← Spec.map_comp, hc, Spec.map_id, Category.id_comp]
  exact AbelianModuli.ReferenceFamily.PEL.Objects.PELObject.complexFiber_paired_rank P (M.complexTestFamily κ f) κ hκ p hp hP j

include hP hM hκ f in
theorem affineTangent_finrank_le_two : Module.finrank ℂ (Derivation ℂ R ℂ) ≤ 2 := by
  let A := (M.complexTestFamily κ f).polarized
  let ρ := (M.complexTestFamily κ f).action
  let hρ := (M.complexTestFamily κ f).rosati
  let U := A.abelian.scheme.left.affineOpenCover
  let hr := affineUniversalFixedFiber_pairedRank M hP κ hκ R f
  let q := PolarizedPELFamilyTangent.Construction.polarizedPELFamilyTangent P hP R A ρ hρ U hr
  have hq : Function.Injective q := by
    intro d e he
    apply M.affineFamilyTangentObstruction_injective hM κ R f U
    exact (PolarizedPELFamilyTangent.Construction.polarizedPELFamilyTangent_eq_iff P hP R A ρ hρ U hr d e).mp he
  exact (LinearMap.finrank_le_finrank_of_injective hq).trans
    (PolarizedPELFamilyTangent.Construction.polarizedPELFamilyForms_finrank_le_two P hP R A ρ hr)

end FinePELModel

end

end OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.FinePELTangentDimension.Construction

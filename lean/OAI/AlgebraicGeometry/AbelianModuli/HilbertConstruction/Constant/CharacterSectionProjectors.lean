import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Constant.StructureSectionEquivalence
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Sheaf.CharacterAverageSectionValues
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Regular.CharacterAverageValues
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Linear.ConjugateRanges

/-! # Character Section Projectors -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Constant.CharacterSectionProjectors

noncomputable section

/-! The actual constant-torsor sheaf projector on every open is conjugate to the rank-one regular character projector over the actual coefficient ring of that open. -/
open _root_.CategoryTheory _root_.AlgebraicGeometry
universe u
variable {K : Type u} [Field K] {S : Scheme.{u}} (c : K →+* Γ(S, ⊤))
    (G : Type u) [CommGroup G] [Fintype G] [HasEnoughRootsOfUnity K (Monoid.exponent G)]

def openRegularCharacterProjector (U : S.Opens) (χ : G →* Kˣ) :
    Module.End Γ(S, U) (G → Γ(S, U)) := by
  letI : Algebra K Γ(S, U) := (Sheaf.CharacterAverageSectionValues.schemeOpenCoefficientMap c U).toAlgebra
  exact Regular.CharacterProjectors.regularCharacterProjector K G Γ(S, U) χ

def openRegularCharacterProjectorRangeEquiv (U : S.Opens) (χ : G →* Kˣ) :
    (openRegularCharacterProjector c G U χ).range ≃ₗ[Γ(S, U)] Γ(S, U) := by
  letI : Algebra K Γ(S, U) := (Sheaf.CharacterAverageSectionValues.schemeOpenCoefficientMap c U).toAlgebra
  exact CharacterProjectionRange.regularCharacterProjectorRangeEquiv K G Γ(S, U) χ

theorem constantCharacterSectionProjector_eq (U : S.Opens) (χ : G →* Kˣ)
    (hG : (Fintype.card G : K) ≠ 0) :
    IdempotentSheafSectionRanges.moduleSheafSectionLinearMap
        (Sheaf.CharacterAverages.sheafCharacterAverage c (StructureRepresentation.constantStructurePushforward S G) (StructureRepresentation.constantStructureRepresentation S G) χ) U =
      (StructureSectionEquivalence.constantStructureSectionEquiv S G U).symm.conjRingEquiv (openRegularCharacterProjector c G U χ) := by
  let : Algebra K Γ(S, U) := (Sheaf.CharacterAverageSectionValues.schemeOpenCoefficientMap c U).toAlgebra
  let e := StructureSectionEquivalence.constantStructureSectionEquiv S G U
  apply LinearMap.ext
  intro s
  apply e.injective
  change e ((Sheaf.CharacterAverages.sheafCharacterAverage c (StructureRepresentation.constantStructurePushforward S G)
      (StructureRepresentation.constantStructureRepresentation S G) χ).app U s) =
    e (e.symm (Regular.CharacterProjectors.regularCharacterProjector K G Γ(S, U) χ (e s)))
  rw [LinearEquiv.apply_symm_apply]
  funext b
  have h := congrArg (fun z => e z b)
    (Sheaf.CharacterAverageSectionValues.sheafCharacterAverage_app c (StructureRepresentation.constantStructurePushforward S G)
      (StructureRepresentation.constantStructureRepresentation S G) χ U s)
  have hv : e ((Sheaf.CharacterAverages.sheafCharacterAverage c (StructureRepresentation.constantStructurePushforward S G)
      (StructureRepresentation.constantStructureRepresentation S G) χ).app U s) b =
        Sheaf.CharacterAverageSectionValues.schemeOpenCoefficientMap c U ((Fintype.card G : K)⁻¹) *
          ∑ a : G, Sheaf.CharacterAverageSectionValues.schemeOpenCoefficientMap c U ((χ a : K)⁻¹) * e s (b * a) := by
    simpa only [e, map_smul, map_sum, Pi.smul_apply, Finset.sum_apply, smul_eq_mul,
      StructureSectionEquivalence.constantStructureSectionEquiv_translate] using h
  exact hv.trans ((Regular.CharacterAverageValues.regularCharacterAverage_apply K G Γ(S, U) χ (e s) b).symm.trans
    (congrArg (fun p : Module.End Γ(S, U) (G → Γ(S, U)) => p (e s) b)
      (Regular.CharacterAverages.regularCharacterAverage_eq_projector K G Γ(S, U) χ hG)))

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Constant.CharacterSectionProjectors

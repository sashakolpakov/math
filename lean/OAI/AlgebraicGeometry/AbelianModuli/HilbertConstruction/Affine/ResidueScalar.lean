import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Localized.ResidueScalar
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.FiberScalar

/-! # Residue Scalar -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Affine.ResidueScalar

noncomputable section

/-! For an actual residue-field point of an affine scheme, restriction to global base coefficients is fully faithful on vector spaces. -/
open _root_.CategoryTheory _root_.AlgebraicGeometry
universe u

theorem affineEvaluation_fractionGenerated (S : Scheme.{u}) [IsAffine S] (x : S) :
    ∀ t : S.residueField x, ∃ a b : Γ(S, ⊤),
      S.Γevaluation x b ≠ 0 ∧ t * S.Γevaluation x b = S.Γevaluation x a := by
  let : Algebra Γ(S, ⊤) (S.presheaf.stalk x) := (S.presheaf.germ ⊤ x trivial).hom.toAlgebra
  have := (isAffineOpen_top S).isLocalization_stalk ⟨x, trivial⟩
  exact Localized.ResidueScalar.fractionGenerated_localization_surjection
    ((isAffineOpen_top S).primeIdealOf ⟨x, trivial⟩).asIdeal.primeCompl
    (S.residue x).hom (S.residue_surjective x)

theorem affineResidue_appTop_restrictScalars_full (S : Scheme.{u}) [IsAffine S] (x : S) :
    (ModuleCat.restrictScalars.{u} (S.fromSpecResidueField x).appTop.hom).Full := by
  let : Field Γ(Spec (S.residueField x), ⊤) :=
    ((Scheme.ΓSpecIso (S.residueField x)).commRingCatIsoToRingEquiv.toMulEquiv.isField
      (Field.toIsField (S.residueField x))).toField
  let e : S.residueField x ≃+* Γ(Spec (S.residueField x), ⊤) :=
    (Scheme.ΓSpecIso (S.residueField x)).commRingCatIsoToRingEquiv.symm
  have hmap (r : Γ(S, ⊤)) : e (S.Γevaluation x r) = (S.fromSpecResidueField x).appTop r := by
    apply e.symm.injective
    exact (e.symm_apply_apply (S.Γevaluation x r)).trans
      (ConcreteCategory.congr_hom (FiberScalar.FiberScalarMaps.fromResidue_appTop S x) r).symm
  have hf := Localized.ResidueScalar.fractionGenerated_postcomp_equiv (S.Γevaluation x).hom (affineEvaluation_fractionGenerated S x) e
  apply Residue.Scalar.restrictScalars_full_of_fractionGenerated (S.fromSpecResidueField x).appTop.hom
  intro t
  obtain ⟨a, b, hb, ht⟩ := hf t
  refine ⟨a, b, ?_, ?_⟩
  · exact (hmap b).symm ▸ hb
  · exact (congrArg (fun z => t * z) (hmap b)).symm.trans (ht.trans (hmap a))

def affineResidueModuleIso (S : Scheme.{u}) [IsAffine S] (x : S)
    {M Q : ModuleCat.{u} Γ(Spec (S.residueField x), ⊤)}
    (e : (ModuleCat.restrictScalars.{u} (S.fromSpecResidueField x).appTop.hom).obj M ≅
      (ModuleCat.restrictScalars.{u} (S.fromSpecResidueField x).appTop.hom).obj Q) : M ≅ Q := by
  have := affineResidue_appTop_restrictScalars_full S x
  exact (ModuleCat.restrictScalars.{u} (S.fromSpecResidueField x).appTop.hom).preimageIso e

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Affine.ResidueScalar

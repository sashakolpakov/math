import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Family.CoefficientModels
import Mathlib.AlgebraicGeometry.Morphisms.Smooth

/-! # Coefficient Family Recovery -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction

noncomputable section

/-! The actual projective coefficient family has smooth recovery when the original closed family is smooth. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

theorem Single.DegreeFamilyModels.ProjectiveFamilyEquations.coefficientFamily_recovery_smooth
    {R : Type u} [CommRing R] {n : ℕ}
    {F : Closed.Families.FlatClosedFamily (Projective.ProjectivePresentations.affineProjectiveSpace R n)} [Smooth F.scheme.hom]
    (E : Single.DegreeFamilyModels.ProjectiveFamilyEquations F) :
    Smooth ((Over.pullback (Spec.map (CommRingCat.ofHom (E.coefficientRing ℤ).val.toRingHom))).obj
      (Projective.EmbeddingBaseChange.homogeneousProjectiveFamily (E.modelIdeal ℤ))).hom := by
  let c := Spec.map (CommRingCat.ofHom (E.coefficientRing ℤ).val.toRingHom)
  let X := Projective.EmbeddingBaseChange.homogeneousProjectiveFamily (E.modelIdeal ℤ)
  let h := E.coefficientModel_isPullback ℤ
  let e : F.scheme ≅ (Over.pullback c).obj X :=
    Over.isoMk h.isoPullback h.isoPullback_hom_snd
  have : IsIso e.inv.left := (Over.forget (Spec (.of R))).map_isIso e.inv
  have hs : Smooth (e.inv.left ≫ F.scheme.hom) := inferInstance
  exact (congrArg Smooth e.inv.w).mp hs

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction

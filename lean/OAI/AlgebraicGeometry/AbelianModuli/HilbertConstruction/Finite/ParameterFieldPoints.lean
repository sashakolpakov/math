import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Affine.OverChartPoints
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Over.IsoMorphismProperty
import Mathlib.AlgebraicGeometry.Morphisms.Finite
import Mathlib.LinearAlgebra.FreeModule.Finite.Matrix

/-! # Parameter Field Points -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Finite.ParameterFieldPoints

noncomputable section

/-! A finite parameter over a field has finitely many points valued in any fixed extension field. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

variable {K F : Type u} [Field K] [Field F] [Algebra K F]

theorem finiteParameter_fieldPoints (M : Over (Spec (.of K))) [IsFinite M.hom] :
    Finite (((algSpec (.of K)).obj (Opposite.op (CommAlgCat.of K F))) ⟶ M) := by
  have : IsAffine M.left := isAffine_of_isAffineHom M.hom
  let R := Affine.OverChartPoints.affineOverAlgebra K M
  have hR : IsFinite (Spec.map (CommRingCat.ofHom (algebraMap K R))) :=
    (HilbertConstruction.Over.IsoMorphismProperty.overIso_morphismProperty_iff (@IsFinite) (Affine.OverChartPoints.affineOverIso K M)).mp inferInstance
  have : Module.Finite K R := (IsFinite.SpecMap_iff _).mp hR
  let e : (((algSpec (.of K)).obj (Opposite.op (CommAlgCat.of K F))) ⟶ M) ≃
      (R ⟶ CommAlgCat.of K F) :=
    ((Iso.refl _).homCongr (Affine.OverChartPoints.affineOverIso K M)).trans
      ((algSpec.fullyFaithful (R := CommRingCat.of K)).homEquiv.symm.trans (opEquiv _ _))
  have : Finite (R ⟶ CommAlgCat.of K F) :=
    Finite.of_injective (fun f : R ⟶ CommAlgCat.of K F => f.hom) (fun _ _ h => CommAlgCat.hom_ext h)
  exact Finite.of_equiv _ e.symm

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Finite.ParameterFieldPoints

import OAI.AlgebraicGeometry.Picard.ThetaConstruction.FiniteCoefficientLineModel
import OAI.AlgebraicGeometry.Picard.ThetaConstruction.GenericFiniteHomogeneityDescent

/-! # Noetherian Homogeneous Line Model -/

namespace OAI.AlgebraicGeometry.Picard.ThetaConstruction.NoetherianHomogeneousLineModel.Geometric

noncomputable section

/-! An arbitrary affine homogeneous family is the actual pullback of
a homogeneous family over a locally Noetherian original test. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory

variable {k R : Type} [CommRing k] [CommRing R] [Algebra k R]

theorem algebraParameterMap_subalgebra_factor
    {B : Type} [CommRing B] [Algebra k B] [Algebra B R] [IsScalarTower k B R]
    (T : Subalgebra B R) :
    AbelianModuli.ReferenceFamily.Finite.CoefficientLimit.algebraSpecMap k (T.val.restrictScalars k) ≫ DoubleFamilyIsoDescent.Geometric.algebraParameterMap k B T =
      DoubleFamilyIsoDescent.Geometric.algebraParameterMap k B R := by
  apply Over.OverMorphism.ext
  change Spec.map _ ≫ Spec.map _ = Spec.map _
  rw [← Spec.map_comp]
  congr 1

theorem exists_noetherian_homogeneous_line_model [IsNoetherianRing k] {g : ℕ}
    (A : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g (Spec (.of k))) (hA : AbelianScheme.IsogenyQuotient.GlobalFunctions.Construction.HasUniversalGlobalFunctions A.scheme)
    (L : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle (AbelianModuli.ReferenceFamily.Finite.CoefficientLimit.algebraSpecOver k R ⊗ A.scheme).left)
    (hL : A.IsHomogeneousPicardClass (AbelianModuli.ReferenceFamily.Finite.CoefficientLimit.algebraSpecOver k R) (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf L)) :
    ∃ (T : Over (Spec (.of k))) (_ : IsLocallyNoetherian T.left)
      (K : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle (T ⊗ A.scheme).left) (j : AbelianModuli.ReferenceFamily.Finite.CoefficientLimit.algebraSpecOver k R ⟶ T),
      A.IsHomogeneousPicardClass T (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf K) ∧
      AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass (j ⊗ₘ 𝟙 A.scheme).left (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf K) =
        AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf L := by
  obtain ⟨s, K, eK⟩ := FiniteCoefficientLineModel.Geometric.exists_finiteType_original_line_model k R A.scheme L
  let B := AbelianModuli.ReferenceFamily.Finite.CoefficientDiagram.finiteCoefficientRing k R s
  have hK : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf (K.pullback (DoubleFamilyIsoDescent.Geometric.algebraParameterMap k B R ⊗ₘ 𝟙 A.scheme).left) =
      AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf L := by
    rw [tensorHom_id]
    exact Quotient.sound eK
  have hKR : A.IsHomogeneousPicardClass (AbelianModuli.ReferenceFamily.Finite.CoefficientLimit.algebraSpecOver k R)
      (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf (K.pullback (DoubleFamilyIsoDescent.Geometric.algebraParameterMap k B R ⊗ₘ 𝟙 A.scheme).left)) :=
    (congrArg (A.IsHomogeneousPicardClass (AbelianModuli.ReferenceFamily.Finite.CoefficientLimit.algebraSpecOver k R)) hK).mpr hL
  obtain ⟨C, hC, hKC⟩ := GenericFiniteHomogeneityDescent.Geometric.exists_fg_homogeneous_parameter_line A hA K hKR
  let : Algebra.FiniteType B C := C.fg_iff_finiteType.mp hC
  let : IsNoetherianRing B := inferInstanceAs (IsNoetherianRing (AbelianModuli.ReferenceFamily.Finite.CoefficientDiagram.finiteCoefficientRing k R s))
  let : IsNoetherianRing C := Algebra.FiniteType.isNoetherianRing B C
  let T := AbelianModuli.ReferenceFamily.Finite.CoefficientLimit.algebraSpecOver k C
  let p := DoubleFamilyIsoDescent.Geometric.algebraParameterMap k B C
  let j := AbelianModuli.ReferenceFamily.Finite.CoefficientLimit.algebraSpecMap k (C.val.restrictScalars k)
  let KC := K.pullback (p ⊗ₘ 𝟙 A.scheme).left
  have hT : IsLocallyNoetherian T.left := inferInstanceAs (IsLocallyNoetherian (Spec (.of C)))
  have hj : j ≫ p = DoubleFamilyIsoDescent.Geometric.algebraParameterMap k B R := algebraParameterMap_subalgebra_factor C
  refine ⟨T, hT, KC, j, hKC, ?_⟩
  exact (RepresentationTheory.Theta.Geometric.ParameterizedPicardClass.parameterLineClass_naturality K p j).trans
    ((congrArg (RepresentationTheory.Theta.Geometric.ParameterizedPicardClass.parameterLineClass K) hj).trans hK)

end

end OAI.AlgebraicGeometry.Picard.ThetaConstruction.NoetherianHomogeneousLineModel.Geometric

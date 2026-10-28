import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.TranslationAffineChart
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Affine.PresentationSectionMorphism

/-! # Translation Open Units -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.TranslationOpenUnits

noncomputable section

/-! The original open-section pullback by infinitesimal translation
has the computed affine coefficients. Dividing by the actual projection
pullback gives exactly the constant-conormal logarithm of the unit. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj

attribute [local implicit_reducible] EtaleSplittingAt.EtaleSplitting.affineOver

variable (G : Over Foundations.Scheme.ProjectiveSpace.complexBase) [IsIntegral G.left] [Smooth G.hom] [GrpObj G]
    (B : CommAlgCat ℂ) (i : EtaleSplittingAt.EtaleSplitting.affineOver ℂ B ⟶ G) [IsOpenImmersion i.left]
    (v : Fin (Betti.AffineDimension.Realization.functionFieldDifferentialDimension G.hom) → ℂ)

theorem nativeTranslationCoefficient_square :
    Affine.AlgebraAutomorphismNaturality.affineOverAlgHom ℂ B (DualNumber B)
        (Affine.ConstantConormalNaturality.affineTranslationCoefficients G B i (IdentityConormalLinear.nativeIdentityConormalLinear G v)) ≫ i =
      InfinitesimalTranslation.dualAffineTranslationChart G B i ≫
        InfinitesimalTranslation.dualInfinitesimalTranslation G (SchemeDualTangent.nativeSchemeTangentDualEquiv G 1 v) := by
  rw [Affine.ConstantConormalNaturality.affineTranslationCoefficients, Affine.OverMorphismAlgebra.affineOverMorphismAlgebra_recovery]
  exact (Affine.ConstantConormalNaturality.affineConstantConormalOpenLift_inclusion G B i (IdentityConormalLinear.nativeIdentityConormalLinear G v)).trans
    (InfinitesimalTranslation.dualAffineTranslationChart_native G B i v).symm

omit [AlgebraicGeometry.IsIntegral G.left] [Smooth G.hom] [GrpObj G] in
theorem nativeProjectionCoefficient_square :
    Affine.AlgebraAutomorphismNaturality.affineOverAlgHom ℂ B (DualNumber B) (TrivSqZeroExt.inlAlgHom ℂ B B) ≫ i =
      InfinitesimalTranslation.dualAffineTranslationChart G B i ≫ snd (LieRanks.dualNumberTest ℂ) G := by
  rw [InfinitesimalTranslation.dualAffineTranslationChart_projection]
  change Dual.CoefficientSchemeTests.dualCoefficientProjection ℂ B ≫ i =
    Dual.CoefficientSchemeTests.dualCoefficientProjection ℂ B ≫ Affine.ChartCoefficientConormal.affineChartCoefficientPoint ℂ B B G i
  rw [Affine.DualMapReductionSquare.affineChartCoefficientPoint_self]

theorem nativeTranslationOpenRange_le :
    (InfinitesimalTranslation.dualAffineTranslationChart G B i).left.opensRange ≤
      (InfinitesimalTranslation.dualInfinitesimalTranslation G (SchemeDualTangent.nativeSchemeTangentDualEquiv G 1 v)).left ⁻¹ᵁ i.left.opensRange :=
  Affine.PresentationSectionMorphism.openRange_preimage_of_square
    (Affine.AlgebraAutomorphismNaturality.affineOverAlgHom ℂ B (DualNumber B)
      (Affine.ConstantConormalNaturality.affineTranslationCoefficients G B i (IdentityConormalLinear.nativeIdentityConormalLinear G v))).left
    i.left (InfinitesimalTranslation.dualAffineTranslationChart G B i).left
    (InfinitesimalTranslation.dualInfinitesimalTranslation G (SchemeDualTangent.nativeSchemeTangentDualEquiv G 1 v)).left
    (congrArg Over.Hom.left (nativeTranslationCoefficient_square G B i v))

omit [AlgebraicGeometry.IsIntegral G.left] [Smooth G.hom] [GrpObj G] in
theorem nativeProjectionOpenRange_le :
    (InfinitesimalTranslation.dualAffineTranslationChart G B i).left.opensRange ≤
      (snd (LieRanks.dualNumberTest ℂ) G).left ⁻¹ᵁ i.left.opensRange :=
  Affine.PresentationSectionMorphism.openRange_preimage_of_square
    (Affine.AlgebraAutomorphismNaturality.affineOverAlgHom ℂ B (DualNumber B) (TrivSqZeroExt.inlAlgHom ℂ B B)).left
    i.left (InfinitesimalTranslation.dualAffineTranslationChart G B i).left (snd (LieRanks.dualNumberTest ℂ) G).left
    (congrArg Over.Hom.left (nativeProjectionCoefficient_square G B i))

theorem nativeTranslationOpenSection (a : B) :
    Affine.PresentationRegularSections.affinePresentationRegularSectionEquiv ℂ (CommAlgCat.of ℂ (DualNumber B))
      (LieRanks.dualNumberTest ℂ ⊗ G) (InfinitesimalTranslation.dualAffineTranslationChart G B i)
      (Affine.ConstantConormalNaturality.affineTranslationCoefficients G B i (IdentityConormalLinear.nativeIdentityConormalLinear G v) a) =
    (InfinitesimalTranslation.dualInfinitesimalTranslation G (SchemeDualTangent.nativeSchemeTangentDualEquiv G 1 v)).left.appLE
      i.left.opensRange (InfinitesimalTranslation.dualAffineTranslationChart G B i).left.opensRange
      (nativeTranslationOpenRange_le G B i v) (Affine.PresentationRegularSections.affinePresentationRegularSectionEquiv ℂ B G i a) :=
  Affine.PresentationSectionMorphism.affinePresentationRegularSectionEquiv_morphism ℂ B (CommAlgCat.of ℂ (DualNumber B))
    (LieRanks.dualNumberTest ℂ ⊗ G) G i (InfinitesimalTranslation.dualAffineTranslationChart G B i)
    (InfinitesimalTranslation.dualInfinitesimalTranslation G (SchemeDualTangent.nativeSchemeTangentDualEquiv G 1 v))
    (Affine.ConstantConormalNaturality.affineTranslationCoefficients G B i (IdentityConormalLinear.nativeIdentityConormalLinear G v))
    (nativeTranslationCoefficient_square G B i v) (nativeTranslationOpenRange_le G B i v) a

omit [AlgebraicGeometry.IsIntegral G.left] [Smooth G.hom] [GrpObj G] in
theorem nativeProjectionOpenSection (a : B) :
    Affine.PresentationRegularSections.affinePresentationRegularSectionEquiv ℂ (CommAlgCat.of ℂ (DualNumber B))
      (LieRanks.dualNumberTest ℂ ⊗ G) (InfinitesimalTranslation.dualAffineTranslationChart G B i) (TrivSqZeroExt.inlAlgHom ℂ B B a) =
    (snd (LieRanks.dualNumberTest ℂ) G).left.appLE i.left.opensRange (InfinitesimalTranslation.dualAffineTranslationChart G B i).left.opensRange
      (nativeProjectionOpenRange_le G B i) (Affine.PresentationRegularSections.affinePresentationRegularSectionEquiv ℂ B G i a) :=
  Affine.PresentationSectionMorphism.affinePresentationRegularSectionEquiv_morphism ℂ B (CommAlgCat.of ℂ (DualNumber B))
    (LieRanks.dualNumberTest ℂ ⊗ G) G i (InfinitesimalTranslation.dualAffineTranslationChart G B i) (snd (LieRanks.dualNumberTest ℂ) G)
    (TrivSqZeroExt.inlAlgHom ℂ B B) (nativeProjectionCoefficient_square G B i)
    (nativeProjectionOpenRange_le G B i) a

theorem nativeTranslationOpenUnitRatio_coefficient (u : Bˣ) :
    let e := Affine.PresentationRegularSections.affinePresentationRegularSectionEquiv ℂ (CommAlgCat.of ℂ (DualNumber B))
      (LieRanks.dualNumberTest ℂ ⊗ G) (InfinitesimalTranslation.dualAffineTranslationChart G B i)
    let q := Units.map (Affine.PresentationRegularSections.affinePresentationRegularSectionEquiv ℂ B G i).toMonoidHom u
    (Units.map e.symm.toMonoidHom
      (Units.map ((InfinitesimalTranslation.dualInfinitesimalTranslation G (SchemeDualTangent.nativeSchemeTangentDualEquiv G 1 v)).left.appLE
        i.left.opensRange (InfinitesimalTranslation.dualAffineTranslationChart G B i).left.opensRange
        (nativeTranslationOpenRange_le G B i v)).hom.toMonoidHom q /
       Units.map ((snd (LieRanks.dualNumberTest ℂ) G).left.appLE i.left.opensRange
        (InfinitesimalTranslation.dualAffineTranslationChart G B i).left.opensRange
        (nativeProjectionOpenRange_le G B i)).hom.toMonoidHom q)).val.snd =
      CoefficientUnitLogarithms.coefficientUnitLog ((Affine.PresentationConormalLinearity.affinePresentationConormalLinearEquiv G B i).symm
        (ConormalUnitLogCoordinates.coefficientCovector B (IdentityConormalLinear.nativeIdentityConormalLinear G v))) u := by
  dsimp only
  have ht (a : B) := (congrArg
    (Affine.PresentationRegularSections.affinePresentationRegularSectionEquiv ℂ (CommAlgCat.of ℂ (DualNumber B))
      (LieRanks.dualNumberTest ℂ ⊗ G) (InfinitesimalTranslation.dualAffineTranslationChart G B i)).symm
    (nativeTranslationOpenSection G B i v a)).symm
  have hp (a : B) := (congrArg
    (Affine.PresentationRegularSections.affinePresentationRegularSectionEquiv ℂ (CommAlgCat.of ℂ (DualNumber B))
      (LieRanks.dualNumberTest ℂ ⊗ G) (InfinitesimalTranslation.dualAffineTranslationChart G B i)).symm
    (nativeProjectionOpenSection G B i a)).symm
  simp only [RingEquiv.symm_apply_apply] at ht hp
  have hu : Units.map
      (Affine.PresentationRegularSections.affinePresentationRegularSectionEquiv ℂ (CommAlgCat.of ℂ (DualNumber B))
        (LieRanks.dualNumberTest ℂ ⊗ G) (InfinitesimalTranslation.dualAffineTranslationChart G B i)).symm.toMonoidHom
      (Units.map ((InfinitesimalTranslation.dualInfinitesimalTranslation G (SchemeDualTangent.nativeSchemeTangentDualEquiv G 1 v)).left.appLE
        i.left.opensRange (InfinitesimalTranslation.dualAffineTranslationChart G B i).left.opensRange
        (nativeTranslationOpenRange_le G B i v)).hom.toMonoidHom
        (Units.map (Affine.PresentationRegularSections.affinePresentationRegularSectionEquiv ℂ B G i).toMonoidHom u)) =
      Units.map (Affine.ConstantConormalNaturality.affineTranslationCoefficients G B i (IdentityConormalLinear.nativeIdentityConormalLinear G v)).toMonoidHom u :=
    Units.ext (ht u.val)
  have hv : Units.map
      (Affine.PresentationRegularSections.affinePresentationRegularSectionEquiv ℂ (CommAlgCat.of ℂ (DualNumber B))
        (LieRanks.dualNumberTest ℂ ⊗ G) (InfinitesimalTranslation.dualAffineTranslationChart G B i)).symm.toMonoidHom
      (Units.map ((snd (LieRanks.dualNumberTest ℂ) G).left.appLE i.left.opensRange
        (InfinitesimalTranslation.dualAffineTranslationChart G B i).left.opensRange
        (nativeProjectionOpenRange_le G B i)).hom.toMonoidHom
        (Units.map (Affine.PresentationRegularSections.affinePresentationRegularSectionEquiv ℂ B G i).toMonoidHom u)) =
      Units.map (TrivSqZeroExt.inlAlgHom ℂ B B).toMonoidHom u := Units.ext (hp u.val)
  rw [map_div, hu, hv]
  exact Affine.ConstantConormalNaturality.affineTranslationUnitRatio_coefficient G B i (IdentityConormalLinear.nativeIdentityConormalLinear G v) u

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.TranslationOpenUnits

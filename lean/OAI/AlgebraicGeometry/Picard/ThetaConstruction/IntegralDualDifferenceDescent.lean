import OAI.AlgebraicGeometry.Picard.ThetaConstruction.IntegralDualCubical
import OAI.RepresentationTheory.Theta.Geometric.DescendedDifferenceAxis
import OAI.RepresentationTheory.Theta.Geometric.Cubical.DifferenceHomogeneity
import OAI.RepresentationTheory.Theta.Geometric.HomogeneousParameterDescent

/-! # Integral Dual Difference Descent -/

namespace OAI.AlgebraicGeometry.Picard.ThetaConstruction

noncomputable section

/-! The actual primitive difference bundle descends to the integral-dual
product. The resulting homogeneous algebraic line bundle is normalized
on both identity axes and pulls back to the exact primitive difference
bundle. Universality is still a further conclusion to prove. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj

variable {g : ℕ} {E : DefinitionsIntegral.IntegralMatrix g} {T : DefinitionsIntegral.MarkedPolarizedTorus g E}
    {M : PeriodModel.Geometric.AlgebraicPeriodModel T} {N : IntegralDualModel.Geometric.IntegralDualAlgebraicModel T}
    (p : IntegralDualIsogenyKernel.Geometric.IntegralDualLatticeIsogeny M N)

theorem IntegralDualIsogenyKernel.Geometric.IntegralDualLatticeIsogeny.differenceBundle_homogeneous (L : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle M.abelianScheme.scheme.left)
    (hL : RepresentationTheory.Theta.Geometric.Intrinsic.CubeClass.nativeCubeDefect M.abelian (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf L) = 1) :
    M.abelianScheme.IsHomogeneousPicardClass M.abelianScheme.scheme
      (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf (RepresentationTheory.Theta.Geometric.AbelianDifferenceBundle.abelianDifferenceBundle M.abelianScheme L)) := by
  apply RepresentationTheory.Theta.Geometric.Cubical.DifferenceHomogeneity.abelianDifferenceBundle_homogeneous M.abelianScheme L
  intro U a b c
  exact RepresentationTheory.Theta.Geometric.Cubical.ClassPullback.nativeCubeClass_pullback M.abelian (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf L) hL a b c

theorem IntegralDualIsogenyKernel.Geometric.IntegralDualLatticeIsogeny.quotientDifference_homogeneous (L : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle M.abelianScheme.scheme.left)
    (hL : RepresentationTheory.Theta.Geometric.Intrinsic.CubeClass.nativeCubeDefect M.abelian (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf L) = 1)
    (Q : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle (N.abelianScheme.scheme ⊗ M.abelianScheme.scheme).left)
    (recover : (Q.pullback (p.isogeny.hom ⊗ₘ 𝟙 M.abelianScheme.scheme).left).sheaf ≅
      (RepresentationTheory.Theta.Geometric.AbelianDifferenceBundle.abelianDifferenceBundle M.abelianScheme L).sheaf) :
    M.abelianScheme.IsHomogeneousPicardClass N.abelianScheme.scheme (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf Q) := by
  apply RepresentationTheory.Theta.Geometric.HomogeneousParameterDescent.homogeneous_of_fppf_parameter_pullback M.abelianScheme Q p.isogeny.hom
  have h : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf (Q.pullback (p.isogeny.hom ⊗ₘ 𝟙 M.abelianScheme.scheme).left) =
      AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf (RepresentationTheory.Theta.Geometric.AbelianDifferenceBundle.abelianDifferenceBundle M.abelianScheme L) := Quotient.sound ⟨recover⟩
  exact (congrArg (M.abelianScheme.IsHomogeneousPicardClass M.abelianScheme.scheme) h).mpr
    (IntegralDualIsogenyKernel.Geometric.IntegralDualLatticeIsogeny.differenceBundle_homogeneous L hL)

theorem IntegralDualIsogenyKernel.Geometric.IntegralDualLatticeIsogeny.exists_normalized_homogeneous_primitive_difference (hE : E.transpose = -E) :
    ∃ (U V : RepresentationTheory.Theta.Geometric.AutomorphicFamilies.CM.Torus.AutomorphicTheta.Family (T.polarizationFactor hE))
      (jU : M.abelian.toOver ⟶ Over.mk (Foundations.Scheme.ProjectiveSpace.projectiveSpaceToBase U.projectiveDimension))
      (jV : M.abelian.toOver ⟶ Over.mk (Foundations.Scheme.ProjectiveSpace.projectiveSpaceToBase V.projectiveDimension))
      (Q : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle (N.abelianScheme.scheme ⊗ M.abelianScheme.scheme).left),
      0 < U.degree ∧ V.degree = U.degree + 1 ∧
      IsClosedImmersion jU.left ∧ IsClosedImmersion jV.left ∧
      (∀ t, ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map jU (M.period t) =
        ComplexPoints.Analytic.ProjectiveScheme.projectivizationSchemePoint U.projectiveDimension (U.projectiveMap t)) ∧
      (∀ t, ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map jV (M.period t) =
        ComplexPoints.Analytic.ProjectiveScheme.projectivizationSchemePoint V.projectiveDimension (V.projectiveMap t)) ∧
      let L := RepresentationTheory.Theta.Geometric.AlgebraicQuotient.algebraicThetaQuotient jU.left jV.left
      L.IsAmple ∧ RepresentationTheory.Theta.Geometric.Intrinsic.CubeClass.nativeCubeDefect M.abelian (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf L) = 1 ∧
      (∀ l m : T.lattice, AbelianModuli.ReferenceFamily.Intrinsic.ChernPairing.nativeChernForm M.abelian L
        (M.nativeIntegralPeriod l) (M.nativeIntegralPeriod m) = (DefinitionsIntegral.Geometric.integralLatticeForm T l m : ℚ)) ∧
      M.abelianScheme.IsHomogeneousPicardClass N.abelianScheme.scheme (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf Q) ∧
      Nonempty ((Q.pullback (p.isogeny.hom ⊗ₘ 𝟙 M.abelianScheme.scheme).left).sheaf ≅
        (RepresentationTheory.Theta.Geometric.AbelianDifferenceBundle.abelianDifferenceBundle M.abelianScheme L).sheaf) ∧
      Nonempty ((Q.pullback (lift (1 : M.abelianScheme.scheme ⟶ N.abelianScheme.scheme)
        (𝟙 M.abelianScheme.scheme)).left).sheaf ≅ AbelianModuli.HilbertConstruction.Line.Bundles.structureModule M.abelianScheme.scheme.left) ∧
      Nonempty ((Q.pullback (lift (𝟙 N.abelianScheme.scheme)
        (1 : N.abelianScheme.scheme ⟶ M.abelianScheme.scheme)).left).sheaf ≅
          AbelianModuli.HilbertConstruction.Line.Bundles.structureModule N.abelianScheme.scheme.left) := by
  obtain ⟨U, V, jU, jV, hpos, hdeg, hjU, hjV, heU, heV, hamp, hcube, hpair, hinv⟩ :=
    M.exists_primitive_cubical_integralDual_invariant_theta hE
  let L := RepresentationTheory.Theta.Geometric.AlgebraicQuotient.algebraicThetaQuotient jU.left jV.left
  have hL : ∀ a : p.isogeny.kernelAt (AbelianModuli.ReferenceFamily.ConstantSectionsOn.ConstantSections.baseTest Foundations.Scheme.ProjectiveSpace.complexBase),
      Nonempty ((L.pullback (RepresentationTheory.Theta.Geometric.DifferenceBundleTranslation.groupTranslation M.abelianScheme.scheme a.val).left).sheaf ≅ L.sheaf) :=
    p.kernel_translation_preserves L hinv
  obtain ⟨labels⟩ := RepresentationTheory.Theta.Geometric.IsogenyKernelLabels.exists_isogenyKernel_labelIso p.isogeny
    (p.isogeny.kernelAt (AbelianModuli.ReferenceFamily.ConstantSectionsOn.ConstantSections.baseTest Foundations.Scheme.ProjectiveSpace.complexBase)) (MulEquiv.refl _)
  let e := (RepresentationTheory.Theta.Geometric.AbelianDifferenceBundle.abelianDifferenceBundle_normalized_left M.abelianScheme L).some
  let Q := RepresentationTheory.Theta.Geometric.DescendedDifferenceBundle.descendedDifferenceBundle p.isogeny labels L hL e
  let recover := RepresentationTheory.Theta.Geometric.DescendedDifferenceBundle.descendedDifferenceBundle_pullbackIso p.isogeny labels L hL e
  exact ⟨U, V, jU, jV, Q, hpos, hdeg, hjU, hjV, heU, heV, hamp, hcube, hpair,
    p.quotientDifference_homogeneous L hcube Q recover, ⟨recover⟩,
    ⟨RepresentationTheory.Theta.Geometric.QuotientDifferenceNormalization.quotientDifference_dualZeroIso p.isogeny L Q recover⟩,
    ⟨RepresentationTheory.Theta.Geometric.DescendedDifferenceAxis.descendedDifferenceBundle_zeroIso p.isogeny labels L hL e⟩⟩

end

end OAI.AlgebraicGeometry.Picard.ThetaConstruction

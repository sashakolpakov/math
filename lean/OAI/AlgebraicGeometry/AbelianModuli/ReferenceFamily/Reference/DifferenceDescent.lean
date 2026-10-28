import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Reference.CubicalTheta
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Reference.KernelLifts
import OAI.RepresentationTheory.Theta.Geometric.DescendedDifferenceAxis
import OAI.RepresentationTheory.Theta.Geometric.Cubical.DifferenceHomogeneity
import OAI.RepresentationTheory.Theta.Geometric.HomogeneousParameterDescent

/-! # Difference Descent -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Reference

noncomputable section

/-! Descend the actual reference difference bundle to the dual-lattice
product. The constructed bundle is homogeneous and normalized on both
axes, with an actual sheaf isomorphism recovering the ample difference
bundle. Picard representability is a further assertion. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj

variable {E : Type} [Field E] [NumberField E] [Algebra ℚ E]
    [NumberField.IsCMField E] {s : ℕ} {P : Datum.RankThreePELDatum E s}
    {z : P.domain} {F : Fiber.ReferenceAnalyticFiber P z} {hP : P.IsAdmissible}
    {M : AlgebraicModel.ReferenceAlgebraicModel F hP} {D : DualModel.ReferenceDualModel F hP}
    (p : IsogenyKernel.ReferenceLatticeIsogeny M D)

theorem IsogenyKernel.ReferenceLatticeIsogeny.differenceBundle_homogeneous (L : HilbertConstruction.Line.Bundles.LineBundle M.abelianScheme.scheme.left)
    (hL : RepresentationTheory.Theta.Geometric.Intrinsic.CubeClass.nativeCubeDefect M.abelian (HilbertConstruction.Line.Bundles.LineBundle.classOf L) = 1) :
    M.abelianScheme.IsHomogeneousPicardClass M.abelianScheme.scheme
      (HilbertConstruction.Line.Bundles.LineBundle.classOf (RepresentationTheory.Theta.Geometric.AbelianDifferenceBundle.abelianDifferenceBundle M.abelianScheme L)) := by
  apply RepresentationTheory.Theta.Geometric.Cubical.DifferenceHomogeneity.abelianDifferenceBundle_homogeneous M.abelianScheme L
  intro T a b c
  exact RepresentationTheory.Theta.Geometric.Cubical.ClassPullback.nativeCubeClass_pullback M.abelian (HilbertConstruction.Line.Bundles.LineBundle.classOf L) hL a b c

theorem IsogenyKernel.ReferenceLatticeIsogeny.quotientDifference_homogeneous (L : HilbertConstruction.Line.Bundles.LineBundle M.abelianScheme.scheme.left)
    (hL : RepresentationTheory.Theta.Geometric.Intrinsic.CubeClass.nativeCubeDefect M.abelian (HilbertConstruction.Line.Bundles.LineBundle.classOf L) = 1)
    (Q : HilbertConstruction.Line.Bundles.LineBundle (D.abelianScheme.scheme ⊗ M.abelianScheme.scheme).left)
    (recover : (Q.pullback (p.isogeny.hom ⊗ₘ 𝟙 M.abelianScheme.scheme).left).sheaf ≅
      (RepresentationTheory.Theta.Geometric.AbelianDifferenceBundle.abelianDifferenceBundle M.abelianScheme L).sheaf) :
    M.abelianScheme.IsHomogeneousPicardClass D.abelianScheme.scheme (HilbertConstruction.Line.Bundles.LineBundle.classOf Q) := by
  apply RepresentationTheory.Theta.Geometric.HomogeneousParameterDescent.homogeneous_of_fppf_parameter_pullback M.abelianScheme Q p.isogeny.hom
  have H : HilbertConstruction.Line.Bundles.LineBundle.classOf (Q.pullback (p.isogeny.hom ⊗ₘ 𝟙 M.abelianScheme.scheme).left) =
      HilbertConstruction.Line.Bundles.LineBundle.classOf (RepresentationTheory.Theta.Geometric.AbelianDifferenceBundle.abelianDifferenceBundle M.abelianScheme L) := Quotient.sound ⟨recover⟩
  exact (congrArg (M.abelianScheme.IsHomogeneousPicardClass M.abelianScheme.scheme) H).mpr
    (IsogenyKernel.ReferenceLatticeIsogeny.differenceBundle_homogeneous (M := M) L hL)

theorem IsogenyKernel.ReferenceLatticeIsogeny.exists_normalized_homogeneous_theta_difference :
    ∃ (U V : RepresentationTheory.Theta.Geometric.AutomorphicFamilies.CM.Torus.AutomorphicTheta.Family (F.polarizationFactor hP))
      (jU : M.abelian.toOver ⟶ Over.mk (Foundations.Scheme.ProjectiveSpace.projectiveSpaceToBase U.projectiveDimension))
      (jV : M.abelian.toOver ⟶ Over.mk (Foundations.Scheme.ProjectiveSpace.projectiveSpaceToBase V.projectiveDimension))
      (Q : HilbertConstruction.Line.Bundles.LineBundle (D.abelianScheme.scheme ⊗ M.abelianScheme.scheme).left),
      0 < U.degree ∧ V.degree = U.degree + 1 ∧
      IsClosedImmersion jU.left ∧ IsClosedImmersion jV.left ∧
      (∀ t, ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map jU (M.period t) =
        ComplexPoints.Analytic.ProjectiveScheme.projectivizationSchemePoint U.projectiveDimension (U.projectiveMap t)) ∧
      (∀ t, ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map jV (M.period t) =
        ComplexPoints.Analytic.ProjectiveScheme.projectivizationSchemePoint V.projectiveDimension (V.projectiveMap t)) ∧
      let L := RepresentationTheory.Theta.Geometric.AlgebraicQuotient.algebraicThetaQuotient jU.left jV.left
      L.IsAmple ∧ RepresentationTheory.Theta.Geometric.Intrinsic.CubeClass.nativeCubeDefect M.abelian (HilbertConstruction.Line.Bundles.LineBundle.classOf L) = 1 ∧
      M.abelianScheme.IsHomogeneousPicardClass D.abelianScheme.scheme (HilbertConstruction.Line.Bundles.LineBundle.classOf Q) ∧
      Nonempty ((Q.pullback (p.isogeny.hom ⊗ₘ 𝟙 M.abelianScheme.scheme).left).sheaf ≅
        (RepresentationTheory.Theta.Geometric.AbelianDifferenceBundle.abelianDifferenceBundle M.abelianScheme L).sheaf) ∧
      Nonempty ((Q.pullback (lift (1 : M.abelianScheme.scheme ⟶ D.abelianScheme.scheme)
        (𝟙 M.abelianScheme.scheme)).left).sheaf ≅ HilbertConstruction.Line.Bundles.structureModule M.abelianScheme.scheme.left) ∧
      Nonempty ((Q.pullback (lift (𝟙 D.abelianScheme.scheme)
        (1 : D.abelianScheme.scheme ⟶ M.abelianScheme.scheme)).left).sheaf ≅
          HilbertConstruction.Line.Bundles.structureModule D.abelianScheme.scheme.left) := by
  obtain ⟨U, V, jU, jV, hpos, hdeg, hjU, hjV, heU, heV, hamp, hcube, hinv⟩ :=
    M.exists_cubical_kernel_invariant_theta
  let L := RepresentationTheory.Theta.Geometric.AlgebraicQuotient.algebraicThetaQuotient jU.left jV.left
  have hL : ∀ a : p.isogeny.kernelAt (ConstantSectionsOn.ConstantSections.baseTest Foundations.Scheme.ProjectiveSpace.complexBase),
      Nonempty ((L.pullback (RepresentationTheory.Theta.Geometric.DifferenceBundleTranslation.groupTranslation M.abelianScheme.scheme a.val).left).sheaf ≅ L.sheaf) :=
    p.kernel_translation_preserves L hinv
  obtain ⟨labels⟩ := RepresentationTheory.Theta.Geometric.IsogenyKernelLabels.exists_isogenyKernel_labelIso p.isogeny
    (p.isogeny.kernelAt (ConstantSectionsOn.ConstantSections.baseTest Foundations.Scheme.ProjectiveSpace.complexBase)) (MulEquiv.refl _)
  let e := (RepresentationTheory.Theta.Geometric.AbelianDifferenceBundle.abelianDifferenceBundle_normalized_left M.abelianScheme L).some
  let Q := RepresentationTheory.Theta.Geometric.DescendedDifferenceBundle.descendedDifferenceBundle p.isogeny labels L hL e
  let recover := RepresentationTheory.Theta.Geometric.DescendedDifferenceBundle.descendedDifferenceBundle_pullbackIso p.isogeny labels L hL e
  exact ⟨U, V, jU, jV, Q, hpos, hdeg, hjU, hjV, heU, heV,
    hamp, hcube, p.quotientDifference_homogeneous L hcube Q recover, ⟨recover⟩,
    ⟨RepresentationTheory.Theta.Geometric.QuotientDifferenceNormalization.quotientDifference_dualZeroIso p.isogeny L Q recover⟩,
    ⟨RepresentationTheory.Theta.Geometric.DescendedDifferenceAxis.descendedDifferenceBundle_zeroIso p.isogeny labels L hL e⟩⟩

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Reference

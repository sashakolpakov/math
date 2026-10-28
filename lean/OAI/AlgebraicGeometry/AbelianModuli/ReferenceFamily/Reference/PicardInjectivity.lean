import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Reference.PointDifference
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Reference.DifferenceDescent
import OAI.RepresentationTheory.Theta.Geometric.PointPicardClassInjectivity
import OAI.RepresentationTheory.Theta.Geometric.ReducedPicardParameterInjectivity

/-! # Picard Injectivity -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Reference

noncomputable section

/-! Distinct parameters of the constructed reference dual-lattice
model give distinct Picard classes. The comparison retains the original
theta coordinates, and extends to reduced finite-type test schemes. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj

variable {E : Type} [Field E] [NumberField E] [Algebra ℚ E]
    [NumberField.IsCMField E] {s : ℕ} {P : Datum.RankThreePELDatum E s}
    {z : P.domain} {F : Fiber.ReferenceAnalyticFiber P z} {hP : P.IsAdmissible}
    {M : AlgebraicModel.ReferenceAlgebraicModel F hP} {D : DualModel.ReferenceDualModel F hP}
    (p : IsogenyKernel.ReferenceLatticeIsogeny M D)

local instance IsogenyKernel.ReferenceLatticeIsogeny.picardTarget_proper : IsProper D.abelianScheme.scheme.hom :=
  D.abelian.variety.presentation.projective.isProper

local instance IsogenyKernel.ReferenceLatticeIsogeny.picardTarget_finiteType : LocallyOfFiniteType D.abelianScheme.scheme.hom := by
  let : Smooth D.abelianScheme.scheme.hom := D.abelian.variety.presentation.smooth
  infer_instance

theorem IsogenyKernel.ReferenceLatticeIsogeny.pointBundleClass_injective
    (U V : RepresentationTheory.Theta.Geometric.AutomorphicFamilies.CM.Torus.AutomorphicTheta.Family (F.polarizationFactor hP)) (hdeg : V.degree = U.degree + 1)
    (f : M.abelian.toOver ⟶ Over.mk (Foundations.Scheme.ProjectiveSpace.projectiveSpaceToBase U.projectiveDimension))
    (g : M.abelian.toOver ⟶ Over.mk (Foundations.Scheme.ProjectiveSpace.projectiveSpaceToBase V.projectiveDimension))
    (hf : ∀ t, ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map f (M.period t) =
      ComplexPoints.Analytic.ProjectiveScheme.projectivizationSchemePoint U.projectiveDimension (U.projectiveMap t))
    (hg : ∀ t, ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map g (M.period t) =
      ComplexPoints.Analytic.ProjectiveScheme.projectivizationSchemePoint V.projectiveDimension (V.projectiveMap t))
    (hcube : RepresentationTheory.Theta.Geometric.Intrinsic.CubeClass.nativeCubeDefect M.abelian (HilbertConstruction.Line.Bundles.LineBundle.classOf (RepresentationTheory.Theta.Geometric.AlgebraicQuotient.algebraicThetaQuotient f.left g.left)) = 1)
    (Q : HilbertConstruction.Line.Bundles.LineBundle (D.abelianScheme.scheme ⊗ M.abelianScheme.scheme).left)
    (recover : (Q.pullback (p.isogeny.hom ⊗ₘ 𝟙 M.abelianScheme.scheme).left).sheaf ≅
      (RepresentationTheory.Theta.Geometric.AbelianDifferenceBundle.abelianDifferenceBundle M.abelianScheme (RepresentationTheory.Theta.Geometric.AlgebraicQuotient.algebraicThetaQuotient f.left g.left)).sheaf) :
    Function.Injective (RepresentationTheory.Theta.Geometric.PointBundleClasses.pointBundleClass Q) := by
  let L := RepresentationTheory.Theta.Geometric.AlgebraicQuotient.algebraicThetaQuotient f.left g.left
  let c := M.pointDifferenceHom L hcube
  have hc (a : ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints M.abelian.toOver) :
      RepresentationTheory.Theta.Geometric.PointBundleClasses.pointBundleClass Q (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map p.isogeny.hom a) = c a :=
    (RepresentationTheory.Theta.Geometric.PointBundleClasses.pointBundleClass_baseChange Q p.isogeny.hom a).symm.trans (RepresentationTheory.Theta.Geometric.PointBundleClasses.pointBundleClass_congr _ _ recover a)
  intro y w hyw
  obtain ⟨a, rfl⟩ := p.complexPoints_surjective y
  obtain ⟨b, rfl⟩ := p.complexPoints_surjective w
  have hab : c a = c b := (hc a).symm.trans (hyw.trans (hc b))
  have hdiv : c (a / b) = 1 := (map_div c a b).trans
    ((congrArg (fun t => t / c b) hab).trans (div_self' _))
  have hkernel := p.pointDifference_eq_one_mem_kernel U V hdeg f g hf hg (a / b) hdiv
  let pmap := M.abelianScheme.mapPoints D.abelianScheme p.isogeny.hom (ConstantSectionsOn.ConstantSections.baseTest Foundations.Scheme.ProjectiveSpace.complexBase)
  change pmap a = pmap b
  apply div_eq_one.mp
  exact (map_div pmap a b).symm.trans hkernel

include p in
theorem IsogenyKernel.ReferenceLatticeIsogeny.exists_normalized_homogeneous_injective_family :
    ∃ Q : HilbertConstruction.Line.Bundles.LineBundle (D.abelianScheme.scheme ⊗ M.abelianScheme.scheme).left,
      M.abelianScheme.IsHomogeneousPicardClass D.abelianScheme.scheme (HilbertConstruction.Line.Bundles.LineBundle.classOf Q) ∧
      (∀ T : Over Foundations.Scheme.ProjectiveSpace.complexBase, RepresentationTheory.Theta.Geometric.ParameterizedPicardClass.parameterPicardClass Q (1 : T ⟶ D.abelianScheme.scheme) =
        HilbertConstruction.Picard.PicardSheaf.trivialPicardClass M.abelianScheme.scheme T) ∧
      Function.Injective (fun x : ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints D.abelianScheme.scheme => RepresentationTheory.Theta.Geometric.ParameterizedPicardClass.parameterPicardClass Q x) ∧
      ∀ (T : Over Foundations.Scheme.ProjectiveSpace.complexBase) [LocallyOfFiniteType T.hom] [IsReduced T.left],
        Function.Injective (fun t : T ⟶ D.abelianScheme.scheme => RepresentationTheory.Theta.Geometric.ParameterizedPicardClass.parameterPicardClass Q t) := by
  obtain ⟨U, V, jU, jV, Q, _, hdeg, _, _, heU, heV, _, hcube, hhom, ⟨recover⟩, ⟨eD⟩, ⟨eA⟩⟩ :=
    p.exists_normalized_homogeneous_theta_difference
  have hinj := RepresentationTheory.Theta.Geometric.PointPicardClassInjectivity.parameterPicardClass_complex_injective M.abelianScheme Q eA
    (p.pointBundleClass_injective U V hdeg jU jV heU heV hcube Q recover)
  refine ⟨Q, hhom, ?_, hinj, ?_⟩
  · intro T
    exact RepresentationTheory.Theta.Geometric.ParameterizedPicardClass.parameterPicardClass_one Q eD T
  · intro T _ _
    exact RepresentationTheory.Theta.Geometric.ReducedPicardParameterInjectivity.parameterPicardClass_reduced_injective Q hinj T

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Reference

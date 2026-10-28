import OAI.AlgebraicGeometry.Picard.ThetaConstruction.IntegralDualRigidity
import OAI.AlgebraicGeometry.Picard.ThetaConstruction.IntegralDualDifferenceDescent
import OAI.RepresentationTheory.Theta.Geometric.PointDifferenceHomomorphism
import OAI.RepresentationTheory.Theta.Geometric.Cubical.ClassPullback
import OAI.RepresentationTheory.Theta.Geometric.PointPicardClassInjectivity
import OAI.RepresentationTheory.Theta.Geometric.ReducedPicardParameterInjectivity

/-! # Integral Dual Point Separation -/

namespace OAI.AlgebraicGeometry.Picard.ThetaConstruction

noncomputable section

/-! The descended primitive family separates actual complex points
of the candidate dual and all reduced finite-type test morphisms. The
kernel is detected by the original theta translation calculation. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj

variable {g : ℕ} {E : DefinitionsIntegral.IntegralMatrix g} {T : DefinitionsIntegral.MarkedPolarizedTorus g E}

def PeriodModel.Geometric.AlgebraicPeriodModel.pointDifferenceHom (M : PeriodModel.Geometric.AlgebraicPeriodModel T)
    (L : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle M.abelian.toOver.left)
    (hcube : RepresentationTheory.Theta.Geometric.Intrinsic.CubeClass.nativeCubeDefect M.abelian (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf L) = 1) :
    ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints M.abelian.toOver →* AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.IsoClass M.abelian.toOver.left where
  toFun := RepresentationTheory.Theta.Geometric.PointBundleClasses.pointBundleClass (RepresentationTheory.Theta.Geometric.AbelianDifferenceBundle.abelianDifferenceBundle M.abelianScheme L)
  map_one' := RepresentationTheory.Theta.Geometric.PointDifferenceHomomorphism.pointDifferenceBundle_class_one M.abelianScheme L
  map_mul' := RepresentationTheory.Theta.Geometric.PointDifferenceHomomorphism.pointDifferenceBundle_class_mul M.abelianScheme L
    (fun _ a b c => RepresentationTheory.Theta.Geometric.Cubical.ClassPullback.nativeCubeClass_pullback M.abelian (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf L) hcube a b c)

variable {M : PeriodModel.Geometric.AlgebraicPeriodModel T} {N : IntegralDualModel.Geometric.IntegralDualAlgebraicModel T}
    (p : IntegralDualIsogenyKernel.Geometric.IntegralDualLatticeIsogeny M N)

theorem IntegralDualIsogenyKernel.Geometric.IntegralDualLatticeIsogeny.complexPoints_surjective : Function.Surjective (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map p.isogeny.hom) := by
  intro y
  obtain ⟨t, rfl⟩ := N.period.surjective y
  obtain ⟨w, rfl⟩ := QuotientAddGroup.mk_surjective t
  exact ⟨M.period (QuotientAddGroup.mk w), p.comparison (QuotientAddGroup.mk w)⟩

variable (hE : E.transpose = -E)
    (U V : RepresentationTheory.Theta.Geometric.AutomorphicFamilies.CM.Torus.AutomorphicTheta.Family (T.polarizationFactor hE)) (hdeg : V.degree = U.degree + 1)
    (jU : M.abelian.toOver ⟶ Over.mk (Foundations.Scheme.ProjectiveSpace.projectiveSpaceToBase U.projectiveDimension))
    (jV : M.abelian.toOver ⟶ Over.mk (Foundations.Scheme.ProjectiveSpace.projectiveSpaceToBase V.projectiveDimension))
    (hU : ∀ t, ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map jU (M.period t) =
      ComplexPoints.Analytic.ProjectiveScheme.projectivizationSchemePoint U.projectiveDimension (U.projectiveMap t))
    (hV : ∀ t, ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map jV (M.period t) =
      ComplexPoints.Analytic.ProjectiveScheme.projectivizationSchemePoint V.projectiveDimension (V.projectiveMap t))

include hdeg hU hV in
theorem IntegralDualIsogenyKernel.Geometric.IntegralDualLatticeIsogeny.pointDifference_eq_one_mem_kernel (a : ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints M.abelian.toOver)
    (ha : RepresentationTheory.Theta.Geometric.PointBundleClasses.pointBundleClass (RepresentationTheory.Theta.Geometric.AbelianDifferenceBundle.abelianDifferenceBundle M.abelianScheme
      (RepresentationTheory.Theta.Geometric.AlgebraicQuotient.algebraicThetaQuotient jU.left jV.left)) a = 1) :
    ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map p.isogeny.hom a = 1 := by
  obtain ⟨t, rfl⟩ := M.period.surjective a
  obtain ⟨w, rfl⟩ := QuotientAddGroup.mk_surjective t
  have H := (RepresentationTheory.Theta.Geometric.PointBundleClasses.pointDifferenceBundle_class M.abelianScheme
    (RepresentationTheory.Theta.Geometric.AlgebraicQuotient.algebraicThetaQuotient jU.left jV.left) (M.period (QuotientAddGroup.mk w))).symm.trans ha
  have H' : RepresentationTheory.Theta.Geometric.Picard.PicardPullback.picardPullback (RepresentationTheory.Theta.Geometric.AlgebraicTranslation.abelianTranslation M.abelian (M.period (QuotientAddGroup.mk w))).left
      (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf (RepresentationTheory.Theta.Geometric.AlgebraicQuotient.algebraicThetaQuotient jU.left jV.left)) =
    AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf (RepresentationTheory.Theta.Geometric.AlgebraicQuotient.algebraicThetaQuotient jU.left jV.left) := mul_inv_eq_one.mp H
  obtain ⟨u⟩ := Quotient.exact H'
  have hw := M.nativeTranslation_mem_integralDual hE U V hdeg jU jV hU hV w u
  have hz : IntegralDualModel.Geometric.integralDualTorusMap T (QuotientAddGroup.mk w) = 0 := by
    change (QuotientAddGroup.mk w : DefinitionsIntegral.Tangent g ⧸ T.integralDualLattice.toAddSubgroup) = 0
    exact (@QuotientAddGroup.eq_zero_iff (DefinitionsIntegral.Tangent g) inferInstance
      T.integralDualLattice.toAddSubgroup inferInstance w).mpr hw
  exact (p.comparison (QuotientAddGroup.mk w)).trans ((congrArg N.period hz).trans N.period_zero)

include hdeg hU hV in
theorem IntegralDualIsogenyKernel.Geometric.IntegralDualLatticeIsogeny.pointBundleClass_injective
    (hcube : RepresentationTheory.Theta.Geometric.Intrinsic.CubeClass.nativeCubeDefect M.abelian (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf (RepresentationTheory.Theta.Geometric.AlgebraicQuotient.algebraicThetaQuotient jU.left jV.left)) = 1)
    (Q : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle (N.abelianScheme.scheme ⊗ M.abelianScheme.scheme).left)
    (recover : (Q.pullback (p.isogeny.hom ⊗ₘ 𝟙 M.abelianScheme.scheme).left).sheaf ≅
      (RepresentationTheory.Theta.Geometric.AbelianDifferenceBundle.abelianDifferenceBundle M.abelianScheme (RepresentationTheory.Theta.Geometric.AlgebraicQuotient.algebraicThetaQuotient jU.left jV.left)).sheaf) :
    Function.Injective (RepresentationTheory.Theta.Geometric.PointBundleClasses.pointBundleClass Q) := by
  let L := RepresentationTheory.Theta.Geometric.AlgebraicQuotient.algebraicThetaQuotient jU.left jV.left
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
  have hk := p.pointDifference_eq_one_mem_kernel hE U V hdeg jU jV hU hV (a / b) hdiv
  let pmap := M.abelianScheme.mapPoints N.abelianScheme p.isogeny.hom (AbelianModuli.ReferenceFamily.ConstantSectionsOn.ConstantSections.baseTest Foundations.Scheme.ProjectiveSpace.complexBase)
  change pmap a = pmap b
  apply div_eq_one.mp
  exact (map_div pmap a b).symm.trans hk

include p hE in
omit U V hdeg jU jV hU hV in
theorem IntegralDualIsogenyKernel.Geometric.IntegralDualLatticeIsogeny.exists_normalized_reduced_picard_separation :
    ∃ Q : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle (N.abelianScheme.scheme ⊗ M.abelianScheme.scheme).left,
      M.abelianScheme.IsHomogeneousPicardClass N.abelianScheme.scheme (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf Q) ∧
      (∀ W : Over Foundations.Scheme.ProjectiveSpace.complexBase, RepresentationTheory.Theta.Geometric.ParameterizedPicardClass.parameterPicardClass Q (1 : W ⟶ N.abelianScheme.scheme) =
        AbelianModuli.HilbertConstruction.Picard.PicardSheaf.trivialPicardClass M.abelianScheme.scheme W) ∧
      Function.Injective (fun x : ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints N.abelianScheme.scheme => RepresentationTheory.Theta.Geometric.ParameterizedPicardClass.parameterPicardClass Q x) ∧
      ∀ (W : Over Foundations.Scheme.ProjectiveSpace.complexBase) [LocallyOfFiniteType W.hom] [IsReduced W.left],
        Function.Injective (fun t : W ⟶ N.abelianScheme.scheme => RepresentationTheory.Theta.Geometric.ParameterizedPicardClass.parameterPicardClass Q t) := by
  obtain ⟨U, V, jU, jV, Q, _hpos, hdeg, _hjU, _hjV, heU, heV, _hamp, hcube, _hpair,
    hhom, ⟨recover⟩, ⟨eD⟩, ⟨eA⟩⟩ := p.exists_normalized_homogeneous_primitive_difference hE
  have hinj := RepresentationTheory.Theta.Geometric.PointPicardClassInjectivity.parameterPicardClass_complex_injective M.abelianScheme Q eA
    (p.pointBundleClass_injective hE U V hdeg jU jV heU heV hcube Q recover)
  refine ⟨Q, hhom, ?_, hinj, ?_⟩
  · intro W
    exact RepresentationTheory.Theta.Geometric.ParameterizedPicardClass.parameterPicardClass_one Q eD W
  · intro W _ _
    exact RepresentationTheory.Theta.Geometric.ReducedPicardParameterInjectivity.parameterPicardClass_reduced_injective Q hinj W

end

end OAI.AlgebraicGeometry.Picard.ThetaConstruction

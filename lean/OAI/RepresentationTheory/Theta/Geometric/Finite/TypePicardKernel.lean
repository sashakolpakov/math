import OAI.RepresentationTheory.Theta.Geometric.NilpotentPicardKernel
import OAI.RepresentationTheory.Theta.Geometric.ReducedPicardParameterInjectivity
import Mathlib.RingTheory.Noetherian.Nilpotent
import Mathlib.RingTheory.FiniteType
import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
import OAI.AlgebraicGeometry.ComplexPoints.Analytic.FiniteTypeSchemeTopology
import OAI.RepresentationTheory.Theta.Geometric.Affine.TestMaps

/-! # Type Picard Kernel -/

namespace OAI.RepresentationTheory.Theta.Geometric.Finite.TypePicardKernel

noncomputable section

section

/-! The actual Picard kernel is trivial on every affine finite-type
complex test, including arbitrary higher-order nilpotent structure. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry OAI.AlgebraicGeometry.ComplexPoints.Analytic.FiniteTypeSchemeTopology
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj

theorem affineTest_locallyOfFiniteType (R : Type) [CommRing R] [Algebra ℂ R]
    [Algebra.FiniteType ℂ R] : LocallyOfFiniteType (OAI.AlgebraicGeometry.Foundations.Scheme.AffineComplexPoints.affineSchemeOver ℂ R).hom := by
  change LocallyOfFiniteType (Spec.map (CommRingCat.ofHom (algebraMap ℂ R)))
  exact (HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)).mpr
    (RingHom.finiteType_algebraMap.mpr inferInstance)

set_option backward.isDefEq.respectTransparency false in
theorem parameterPicardClass_finiteType_kernel
    {n : ℕ} (A : OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme n OAI.AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase) {P : Over OAI.AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase} [GrpObj P]
    [LocallyOfFiniteType P.hom] [IsSeparated P.hom]
    (Q : OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle (P ⊗ A.scheme).left)
    (eQ : (Q.pullback (lift (𝟙 P) (1 : P ⟶ A.scheme)).left).sheaf ≅ OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles.structureModule P.left)
    (hinj : Function.Injective (fun t : OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.LieRanks.dualNumberTest ℂ ⟶ P => ParameterizedPicardClass.parameterPicardClass Q t))
    (hpoints : Function.Injective (fun t : OAI.AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints P => ParameterizedPicardClass.parameterPicardClass Q t))
    {R : Type} [CommRing R] [Algebra ℂ R] [Algebra.FiniteType ℂ R]
    (r : OAI.AlgebraicGeometry.Foundations.Scheme.AffineComplexPoints.affineSchemeOver ℂ R ⟶ P)
    (hQ : ParameterizedPicardClass.parameterPicardClass Q r = ParameterizedPicardClass.parameterPicardClass Q (1 : OAI.AlgebraicGeometry.Foundations.Scheme.AffineComplexPoints.affineSchemeOver ℂ R ⟶ P)) : r = 1 := by
  have : IsNoetherianRing R := Algebra.FiniteType.isNoetherianRing ℂ R
  let R₀ := R ⧸ nilradical R
  have : _root_.IsReduced R₀ := (Ideal.isRadical_iff_quotient_reduced (nilradical R)).mp
    (Ideal.radical_isRadical (0 : Ideal R))
  have : LocallyOfFiniteType (OAI.AlgebraicGeometry.Foundations.Scheme.AffineComplexPoints.affineSchemeOver ℂ R₀).hom := affineTest_locallyOfFiniteType R₀
  have : IsReduced (OAI.AlgebraicGeometry.Foundations.Scheme.AffineComplexPoints.affineSchemeOver ℂ R₀).left := inferInstanceAs (IsReduced (Spec (.of R₀)))
  have hr : NestedReductionMaps.complexReductionMap (nilradical R) ≫ r = 1 :=
    ReducedPicardParameterInjectivity.parameterPicardClass_reduced_injective Q hpoints (OAI.AlgebraicGeometry.Foundations.Scheme.AffineComplexPoints.affineSchemeOver ℂ R₀)
      (NilpotentPicardKernel.parameterPicardClass_kernel_restrict Q r (NestedReductionMaps.complexReductionMap (nilradical R)) hQ)
  exact NilpotentPicardKernel.parameterPicardClass_nilpotent_relative_kernel A Q eQ hinj (nilradical R)
    (IsNoetherianRing.isNilpotent_nilradical R) r hr hQ

end

section

/-! Affine finite-type kernel separation glues on every locally
finite-type test scheme, without any reducedness assumption. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry OAI.AlgebraicGeometry.ComplexPoints.Analytic.FiniteTypeSchemeTopology
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency false in
theorem parameterPicardClass_locallyFiniteType_kernel
    {n : ℕ} (A : OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme n OAI.AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase) {P : Over OAI.AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase} [GrpObj P]
    [LocallyOfFiniteType P.hom] [IsSeparated P.hom]
    (Q : OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle (P ⊗ A.scheme).left)
    (eQ : (Q.pullback (lift (𝟙 P) (1 : P ⟶ A.scheme)).left).sheaf ≅ OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles.structureModule P.left)
    (hinj : Function.Injective (fun t : OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.LieRanks.dualNumberTest ℂ ⟶ P => ParameterizedPicardClass.parameterPicardClass Q t))
    (hpoints : Function.Injective (fun t : OAI.AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints P => ParameterizedPicardClass.parameterPicardClass Q t))
    (T : Over OAI.AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase) [LocallyOfFiniteType T.hom] (r : T ⟶ P)
    (hQ : ParameterizedPicardClass.parameterPicardClass Q r = ParameterizedPicardClass.parameterPicardClass Q (1 : T ⟶ P)) : r = 1 := by
  apply Over.OverMorphism.ext
  apply T.left.affineCover.hom_ext
  intro j
  let X : Over OAI.AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase := Over.mk (T.left.affineCover.f j ≫ T.hom)
  let i : X ⟶ T := Over.homMk (T.left.affineCover.f j)
  have : IsAffine X.left := inferInstanceAs (IsAffine (T.left.affineCover.X j))
  have : LocallyOfFiniteType X.hom := by
    change LocallyOfFiniteType (T.left.affineCover.f j ≫ T.hom)
    infer_instance
  have : Algebra.FiniteType ℂ Γ(X.left, ⊤) := OAI.AlgebraicGeometry.ComplexPoints.Analytic.FiniteTypeSchemeTopology.affineOverGamma_finiteType X
  let e := OAI.AlgebraicGeometry.Foundations.Scheme.AffineSchemeComplexPoints.affineOverIso X
  have ha : e.inv ≫ i ≫ r = 1 := parameterPicardClass_finiteType_kernel A Q eQ hinj hpoints
    (e.inv ≫ i ≫ r) (NilpotentPicardKernel.parameterPicardClass_kernel_restrict Q r (e.inv ≫ i) hQ)
  have hir : i ≫ r = 1 := by
    have H := congrArg (fun a => e.hom ≫ a) ha
    simpa only [Category.assoc, Iso.hom_inv_id_assoc, MonObj.comp_one] using H
  change (i ≫ r).left = (i ≫ (1 : T ⟶ P)).left
  rw [hir]
  simp

end

/-! An affine test map into a finite-type affine parameter scheme
factors through the actual finitely generated image algebra. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry OAI.AlgebraicGeometry.ComplexPoints.Analytic.FiniteTypeSchemeTopology

theorem exists_fg_affineTest_factorization
    (X : Over OAI.AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase) [IsAffine X.left] [LocallyOfFiniteType X.hom]
    {R : Type} [CommRing R] [Algebra ℂ R] (r : OAI.AlgebraicGeometry.Foundations.Scheme.AffineComplexPoints.affineSchemeOver ℂ R ⟶ X) :
    ∃ S : Subalgebra ℂ R, S.FG ∧ ∃ rS : OAI.AlgebraicGeometry.Foundations.Scheme.AffineComplexPoints.affineSchemeOver ℂ S ⟶ X,
      OAI.AlgebraicGeometry.Foundations.Scheme.AffineComplexPoints.affineAlgHomOverSpecEquiv ℂ S R S.val ≫ rS = r := by
  have : Algebra.FiniteType ℂ Γ(X.left, ⊤) := OAI.AlgebraicGeometry.ComplexPoints.Analytic.FiniteTypeSchemeTopology.affineOverGamma_finiteType X
  let f := (Affine.TestMaps.affineTestMapEquiv X R).symm r
  have : Algebra.FiniteType ℂ f.range := Algebra.FiniteType.of_surjective f.rangeRestrict
    f.rangeRestrict_surjective
  refine ⟨f.range, f.range.fg_iff_finiteType.mpr inferInstance,
    Affine.TestMaps.affineTestMapEquiv X f.range f.rangeRestrict, ?_⟩
  rw [Affine.TestMaps.affineTestMapEquiv_comp]
  have hf : f.range.val.comp f.rangeRestrict = f := by ext a; rfl
  rw [hf]
  exact (Affine.TestMaps.affineTestMapEquiv X R).apply_symm_apply r

end

end OAI.RepresentationTheory.Theta.Geometric.Finite.TypePicardKernel

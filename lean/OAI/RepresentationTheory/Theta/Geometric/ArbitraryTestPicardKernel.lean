import OAI.RepresentationTheory.Theta.Geometric.Finite.FactoredPicardKernel
import OAI.RepresentationTheory.Theta.Geometric.OpenRegularFunctionValues
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.DualOpen.Lifts

/-! # Arbitrary Test Picard Kernel -/

namespace OAI.RepresentationTheory.Theta.Geometric.ArbitraryTestPicardKernel

noncomputable section

/-! Picard parameter separation on arbitrary complex test schemes,
including nonnoetherian rings and unbounded nilpotent structure. -/

set_option backward.isDefEq.respectTransparency false
open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj

theorem parameterPicardClass_arbitraryTest_kernel
    {n : ℕ} (A : AlgebraicGeometry.AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme n AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase) {P : Over AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase} [GrpObj P]
    [LocallyOfFiniteType P.hom] [IsSeparated P.hom]
    (Q : AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle (P ⊗ A.scheme).left)
    (eQ : (Q.pullback (lift (𝟙 P) (1 : P ⟶ A.scheme)).left).sheaf ≅ AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles.structureModule P.left)
    (hinj : Function.Injective (fun t : AlgebraicGeometry.AbelianModuli.ReferenceFamily.LieRanks.dualNumberTest ℂ ⟶ P => ParameterizedPicardClass.parameterPicardClass Q t))
    (hpoints : Function.Injective (fun t : AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints P => ParameterizedPicardClass.parameterPicardClass Q t))
    (T : Over AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase) (r : T ⟶ P)
    (hQ : ParameterizedPicardClass.parameterPicardClass Q r = ParameterizedPicardClass.parameterPicardClass Q (1 : T ⟶ P)) : r = 1 := by
  apply Over.OverMorphism.ext
  apply Scheme.hom_ext_of_forall
  intro t
  obtain ⟨V, hV, htV, _⟩ := exists_isAffineOpen_mem_and_subset
    (show r.left t ∈ (⊤ : P.left.Opens) by trivial)
  obtain ⟨U, hU, htU, hUV⟩ := exists_isAffineOpen_mem_and_subset
    (show t ∈ r.left ⁻¹ᵁ V from htV)
  let X := OpenRegularFunctionValues.regularOpenScheme T U
  let Y := OpenRegularFunctionValues.regularOpenScheme P V
  let j := OpenRegularFunctionValues.regularOpenInclusion T U
  let k := OpenRegularFunctionValues.regularOpenInclusion P V
  have : IsAffine X.left := hU
  have : IsAffine Y.left := hV
  have : LocallyOfFiniteType Y.hom := by
    change LocallyOfFiniteType (V.ι ≫ P.hom)
    infer_instance
  have hRange : Set.range (j ≫ r).left ⊆ Set.range k.left := by
    rintro _ ⟨z, rfl⟩
    refine ⟨⟨r.left z.val, hUV z.property⟩, rfl⟩
  let q := AlgebraicGeometry.AbelianModuli.ReferenceFamily.DualOpen.Lifts.overOpenLift k (j ≫ r) hRange
  have hq : q ≫ k = j ≫ r := AlgebraicGeometry.AbelianModuli.ReferenceFamily.DualOpen.Lifts.overOpenLift_fac k (j ≫ r) hRange
  let e := AlgebraicGeometry.Foundations.Scheme.AffineSchemeComplexPoints.affineOverIso X
  have ha : (e.inv ≫ q) ≫ k = 1 := Finite.FactoredPicardKernel.parameterPicardClass_affine_factored_kernel A Q eQ hinj hpoints
    Y k (e.inv ≫ q) (by
      rw [Category.assoc, hq, ← Category.assoc]
      exact NilpotentPicardKernel.parameterPicardClass_kernel_restrict Q r (e.inv ≫ j) hQ)
  have hj : j ≫ r = 1 := by
    have H := congrArg (fun a => e.hom ≫ a) ha
    simpa only [Category.assoc, Iso.hom_inv_id_assoc, hq, MonObj.comp_one] using H
  refine ⟨U, htU, ?_⟩
  change (j ≫ r).left = (j ≫ (1 : T ⟶ P)).left
  rw [hj]
  simp

end

end OAI.RepresentationTheory.Theta.Geometric.ArbitraryTestPicardKernel

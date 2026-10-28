import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.ParameterTangentLinear
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Reference.StructureBound
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Reference.DualModel
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Dual.AffineDiagonal
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-! # Dual Line Universality -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Reference

noncomputable section

section

/-! The actual reference Picard parameter tangent map is bijective:
its native source has dimension 3s, and algebraic H1 has dimension at most 3s. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj

variable {E : Type} [Field E] [NumberField E] [Algebra ℚ E]
    [NumberField.IsCMField E] {s : ℕ} {P : Datum.RankThreePELDatum E s}
    {z : P.domain} {F : Fiber.ReferenceAnalyticFiber P z} {hP : P.IsAdmissible}
    (M : AlgebraicModel.ReferenceAlgebraicModel F hP) (D : DualModel.ReferenceDualModel F hP)

local instance AlgebraicModel.ReferenceAlgebraicModel.tangentBijection_sourceIntegral : IsIntegral D.abelianScheme.scheme.left := D.abelian.variety.property
local instance AlgebraicModel.ReferenceAlgebraicModel.tangentBijection_sourceSmooth : Smooth D.abelianScheme.scheme.hom := D.abelian.variety.presentation.smooth
local instance AlgebraicModel.ReferenceAlgebraicModel.tangentBijection_targetIntegral : IsIntegral M.abelianScheme.scheme.left := M.abelian.variety.property
local instance AlgebraicModel.ReferenceAlgebraicModel.tangentBijection_targetSmooth : Smooth M.abelianScheme.scheme.hom := M.abelian.variety.presentation.smooth
local instance AlgebraicModel.ReferenceAlgebraicModel.tangentBijection_targetProper : IsProper M.abelianScheme.scheme.hom :=
  M.abelian.variety.presentation.projective.isProper
local instance AlgebraicModel.ReferenceAlgebraicModel.tangentBijection_affineDiagonal :
    IsAffineHom (CategoryTheory.Limits.pullback.diagonal
      (CategoryTheory.Limits.terminal.from (LieRanks.dualNumberTest ℂ ⊗ M.abelianScheme.scheme).left)) :=
  Dual.AffineDiagonal.dualFamily_affineDiagonal M.abelianScheme.scheme

theorem AlgebraicModel.ReferenceAlgebraicModel.referenceParameterTangent_bijective
    (Q : HilbertConstruction.Line.Bundles.LineBundle (D.abelianScheme.scheme ⊗ M.abelianScheme.scheme).left)
    (eD : (Q.pullback (lift (1 : M.abelianScheme.scheme ⟶ D.abelianScheme.scheme)
      (𝟙 M.abelianScheme.scheme)).left).sheaf ≅ HilbertConstruction.Line.Bundles.structureModule M.abelianScheme.scheme.left)
    (eA : (Q.pullback (lift (𝟙 D.abelianScheme.scheme)
      (1 : D.abelianScheme.scheme ⟶ M.abelianScheme.scheme)).left).sheaf ≅ HilbertConstruction.Line.Bundles.structureModule D.abelianScheme.scheme.left)
    (hmul : ∀ x y : LieRanks.dualNumberTest ℂ ⟶ D.abelianScheme.scheme,
      RepresentationTheory.Theta.Geometric.ParameterizedPicardClass.parameterPicardClass Q (x * y) = RepresentationTheory.Theta.Geometric.ParameterizedPicardClass.parameterPicardClass Q x * RepresentationTheory.Theta.Geometric.ParameterizedPicardClass.parameterPicardClass Q y)
    (hinj : Function.Injective (fun t : LieRanks.dualNumberTest ℂ ⟶ D.abelianScheme.scheme => RepresentationTheory.Theta.Geometric.ParameterizedPicardClass.parameterPicardClass Q t)) :
    Function.Bijective (Intrinsic.ParameterTangentCohomology.nativeParameterTangentClass M.abelianScheme Q eD) := by
  let := StructureComplexScalars.structureH1ComplexModule M.abelianScheme.scheme
  let : FiniteDimensional ℂ (SheafCohomology.AffineH.Projective.H (HilbertConstruction.Line.Bundles.structureModule M.abelianScheme.scheme.left) 1) :=
    M.referenceStructureH1_finiteDimensional
  have hf := Intrinsic.ParameterTangentLinear.nativeParameterTangentLinear_injective M.abelianScheme Q eD eA hmul hinj
  have hd : Betti.AffineDimension.Realization.functionFieldDifferentialDimension D.abelianScheme.scheme.hom = 3 * s :=
    D.dimension
  have hle : Module.finrank ℂ (SheafCohomology.AffineH.Projective.H (HilbertConstruction.Line.Bundles.structureModule M.abelianScheme.scheme.left) 1) ≤
      Module.finrank ℂ (Fin (Betti.AffineDimension.Realization.functionFieldDifferentialDimension D.abelianScheme.scheme.hom) → ℂ) := by
    rw [Module.finrank_fin_fun, hd]
    exact M.referenceStructureH1_finrank_le_dimension
  have heq := le_antisymm (LinearMap.finrank_le_finrank_of_injective hf) hle
  exact ⟨hf, (LinearMap.injective_iff_surjective_of_finrank_eq_finrank heq).mp hf⟩

end

/-! Every actual line bundle on the reference dual-number family
with trivial reduced fiber is the pullback at a unique original
infinitesimal parameter. The comparison is an actual sheaf isomorphism. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj

variable {E : Type} [Field E] [NumberField E] [Algebra ℚ E]
    [NumberField.IsCMField E] {s : ℕ} {P : Datum.RankThreePELDatum E s}
    {z : P.domain} {F : Fiber.ReferenceAnalyticFiber P z} {hP : P.IsAdmissible}
    (M : AlgebraicModel.ReferenceAlgebraicModel F hP) (D : DualModel.ReferenceDualModel F hP)

local instance AlgebraicModel.ReferenceAlgebraicModel.dualUniversality_sourceIntegral : IsIntegral D.abelianScheme.scheme.left := D.abelian.variety.property
local instance AlgebraicModel.ReferenceAlgebraicModel.dualUniversality_sourceSmooth : Smooth D.abelianScheme.scheme.hom := D.abelian.variety.presentation.smooth
local instance AlgebraicModel.ReferenceAlgebraicModel.dualUniversality_targetIntegral : IsIntegral M.abelianScheme.scheme.left := M.abelian.variety.property
local instance AlgebraicModel.ReferenceAlgebraicModel.dualUniversality_targetSmooth : Smooth M.abelianScheme.scheme.hom := M.abelian.variety.presentation.smooth
local instance AlgebraicModel.ReferenceAlgebraicModel.dualUniversality_targetProper : IsProper M.abelianScheme.scheme.hom :=
  M.abelian.variety.presentation.projective.isProper
local instance AlgebraicModel.ReferenceAlgebraicModel.dualUniversality_affineDiagonal :
    IsAffineHom (CategoryTheory.Limits.pullback.diagonal
      (CategoryTheory.Limits.terminal.from (LieRanks.dualNumberTest ℂ ⊗ M.abelianScheme.scheme).left)) :=
  Dual.AffineDiagonal.dualFamily_affineDiagonal M.abelianScheme.scheme

theorem AlgebraicModel.ReferenceAlgebraicModel.exists_unique_dualParameter_iso
    (Q : HilbertConstruction.Line.Bundles.LineBundle (D.abelianScheme.scheme ⊗ M.abelianScheme.scheme).left)
    (eD : (Q.pullback (lift (1 : M.abelianScheme.scheme ⟶ D.abelianScheme.scheme)
      (𝟙 M.abelianScheme.scheme)).left).sheaf ≅ HilbertConstruction.Line.Bundles.structureModule M.abelianScheme.scheme.left)
    (eA : (Q.pullback (lift (𝟙 D.abelianScheme.scheme)
      (1 : D.abelianScheme.scheme ⟶ M.abelianScheme.scheme)).left).sheaf ≅ HilbertConstruction.Line.Bundles.structureModule D.abelianScheme.scheme.left)
    (hmul : ∀ x y : LieRanks.dualNumberTest ℂ ⟶ D.abelianScheme.scheme,
      RepresentationTheory.Theta.Geometric.ParameterizedPicardClass.parameterPicardClass Q (x * y) = RepresentationTheory.Theta.Geometric.ParameterizedPicardClass.parameterPicardClass Q x * RepresentationTheory.Theta.Geometric.ParameterizedPicardClass.parameterPicardClass Q y)
    (hinj : Function.Injective (fun t : LieRanks.dualNumberTest ℂ ⟶ D.abelianScheme.scheme => RepresentationTheory.Theta.Geometric.ParameterizedPicardClass.parameterPicardClass Q t))
    (L : HilbertConstruction.Line.Bundles.LineBundle (LieRanks.dualNumberTest ℂ ⊗ M.abelianScheme.scheme).left)
    (eL : (Scheme.Modules.pullback (RepresentationTheory.Theta.Geometric.Dual.BaseChangeReduction.dualBaseChangeReduction M.abelianScheme.scheme).left).obj L.sheaf ≅
      HilbertConstruction.Line.Bundles.structureModule M.abelianScheme.scheme.left) :
    ∃! t : DualOpen.Lifts.DualSchemePoints D.abelianScheme.scheme 1,
      Nonempty ((Q.pullback (t.val ⊗ₘ 𝟙 M.abelianScheme.scheme).left).sheaf ≅ L.sheaf) := by
  obtain ⟨v, hv⟩ := (M.referenceParameterTangent_bijective D Q eD eA hmul hinj).surjective
    (DualLine.DeformationClass.dualLineDeformationClass M.abelianScheme.scheme L eL)
  let t := Intrinsic.SchemeDualTangent.nativeSchemeTangentDualEquiv D.abelianScheme.scheme 1 v
  have hc := hv.trans (DualLine.ClassKernel.dualLineKernelCohomology_of_line M.abelianScheme.scheme L eL).symm
  have h := DualLine.ClassKernel.dualLineKernelClassHom_injective M.abelianScheme.scheme (congrArg Multiplicative.ofAdd hc)
  have ht : Nonempty ((Q.pullback (t.val ⊗ₘ 𝟙 M.abelianScheme.scheme).left).sheaf ≅ L.sheaf) :=
    Quotient.exact (congrArg Subtype.val h)
  refine ⟨t, ht, ?_⟩
  intro u hu
  apply Subtype.ext
  apply hinj
  exact congrArg ((HilbertConstruction.Picard.PicardSheaf.toRelativePicard M.abelianScheme.scheme).app (.op (LieRanks.dualNumberTest ℂ)))
    (Quotient.sound ⟨hu.some ≪≫ ht.some.symm⟩)

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Reference

import OAI.AlgebraicGeometry.PELModuli.IntegralModel.PointedGroupFamily
import OAI.AlgebraicGeometry.PELModuli.IntegralModel.WordGeneration
import OAI.AlgebraicGeometry.PELModuli.IntegralModel.GeneratingDimensionSpecialization

/-! # Pointed Family Specialization -/

namespace OAI.AlgebraicGeometry.PELModuli.IntegralModel.PointedFamilySpecialization.Coefficients

noncomputable section

/-! Apply the constructed pointed group family to obtain an arithmetic
generating fiber of exactly the original complex target dimension. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj

variable {R : Type} [Field R] [NumberField R] [Algebra R ℂ]
  (X : Over (Spec (.of R)))
  (x₀ : 𝟙_ (Over (Spec (.of R))) ⟶ X)
  (A : Over (Spec (.of ℂ))) [GrpObj A]
  (a : (Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap R ℂ)))).obj X ⟶ A)
  {m : ℕ}

theorem arithmetic_specialization_of_pointed_family
    [Smooth X.hom] [IsProper X.hom] [GeometricallyConnected X.hom]
    (D : PointedGroupFamily.Coefficients.PointedGroupCoefficientFamily R ℂ X x₀ A a m)
    (n : ℕ) (hn : Surjective (Words.DifferenceWords.map a n).left)
    (N : ℕ) (hN : N ≠ 0) :
    ∃ (B : Base.ArithmeticBaseExtension R (algebraMap R ℂ))
      (p : Over.mk B.fieldExtension ⟶ Fixed.CoefficientModels.Coefficients.coefficientParameter R ℂ D.coefficients),
      letI := D.group
      B.denominator = N ∧
      Surjective ((Over.pullback p.left).map (Words.DifferenceWords.map D.map n)).left ∧
      topologicalKrullDim A.left = topologicalKrullDim ((Over.pullback
        (Spec.map (CommRingCat.ofHom B.embedding) ≫ p.left)).obj D.target).left := by
  let groupD : GrpObj D.target := D.group
  have : IsCommMonObj D.target := D.commutative
  have : Smooth D.target.hom := D.smooth
  have : IsProper D.target.hom := D.proper
  let S := Fixed.CoefficientModels.Coefficients.coefficientParameter R ℂ D.coefficients
  let M : Over S.left := (Over.pullback (Fixed.CoefficientModels.Coefficients.parameterBaseMap R ℂ D.coefficients)).obj X
  let Y : Over S.left := D.target
  let groupY : GrpObj Y := D.group
  have : IsCommMonObj Y := D.commutative
  have : Smooth Y.hom := D.smooth
  have : IsProper Y.hom := D.proper
  have : LocallyOfFiniteType S.hom := Fixed.CoefficientModels.Coefficients.coefficientParameter_locallyOfFiniteType R ℂ D.coefficients
  have : Smooth M.hom := inferInstanceAs
    (Smooth (pullback.snd X.hom (Fixed.CoefficientModels.Coefficients.parameterBaseMap R ℂ D.coefficients)))
  have : IsProper M.hom := inferInstanceAs
    (IsProper (pullback.snd X.hom (Fixed.CoefficientModels.Coefficients.parameterBaseMap R ℂ D.coefficients)))
  have : GeometricallyConnected M.hom := inferInstanceAs
    (GeometricallyConnected (pullback.snd X.hom (Fixed.CoefficientModels.Coefficients.parameterBaseMap R ℂ D.coefficients)))
  let g : Spec (.of ℂ) ⟶ S.left := ArithmeticGeometry.Models.CoefficientSystem.Constructions.Foundations.genericBaseMap R ℂ D.coefficients
  have : IsSchemeTheoreticallyDominant g := ArithmeticGeometry.Models.SpreadingOut.GenericFaithfulness.Construction.spec_injective_schematically_dominant
    (algebraMap (ArithmeticGeometry.Models.CoefficientSystem.Constructions.Foundations.coefficientRing R ℂ D.coefficients) ℂ) Subtype.val_injective
  have : IsDominant g := inferInstance
  let r : M ⟶ Y := D.map
  let eX : (Over.pullback g).obj M ≅
      (Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap R ℂ)))).obj X := D.sourceIso
  let eY : (Over.pullback g).obj Y ≅ A := D.targetIso
  have : IsMonHom eY.hom := D.targetIso_group
  have hg : Surjective ((Over.pullback g).map (Words.DifferenceWords.map r n)).left :=
    WordGeneration.DifferenceWords.surjective_baseChanged_word_of_comparison g (X := M) (A := Y)
      r a eX eY D.comparison n hn
  obtain ⟨B, p, hB, hp, hd⟩ := GeneratingDimensionSpecialization.arithmetic_generating_equal_dimension_specialization
    (algebraMap R ℂ) S M Y r g n hg N hN
  have : IsIso D.targetIso.hom.left :=
    ((Over.forget (Spec (.of ℂ))).mapIso D.targetIso).isIso_hom
  have he : topologicalKrullDim ((Over.pullback g).obj D.target).left =
      topologicalKrullDim A.left :=
    D.targetIso.hom.left.homeomorph.isHomeomorph.topologicalKrullDim_eq
  exact ⟨B, p, hB, hp, he.symm.trans hd⟩

/-- Starting with the complex pointed generating map constructs the whole
finite coefficient diagram and an arithmetic fiber of the same dimension. -/
theorem arithmetic_generating_family_exists
    [Smooth X.hom] [IsProper X.hom] [GeometricallyConnected X.hom]
    [IsCommMonObj A] [Smooth A.hom]
    (i : A ⟶ AbelianModuli.HilbertConstruction.Projective.ProjectivePresentations.affineProjectiveSpace ℂ m) [IsClosedImmersion i.left]
    (ha : Section.Comparisons.mappedSection (Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap R ℂ)))) x₀ ≫ a = 1)
    (n : ℕ) (hn : Surjective (Words.DifferenceWords.map a n).left)
    (N : ℕ) (hN : N ≠ 0) :
    ∃ (D : PointedGroupFamily.Coefficients.PointedGroupCoefficientFamily R ℂ X x₀ A a m)
      (B : Base.ArithmeticBaseExtension R (algebraMap R ℂ))
      (p : Over.mk B.fieldExtension ⟶ Fixed.CoefficientModels.Coefficients.coefficientParameter R ℂ D.coefficients),
      letI := D.group
      B.denominator = N ∧
      Surjective ((Over.pullback p.left).map (Words.DifferenceWords.map D.map n)).left ∧
      topologicalKrullDim A.left = topologicalKrullDim ((Over.pullback
        (Spec.map (CommRingCat.ofHom B.embedding) ≫ p.left)).obj D.target).left := by
  obtain ⟨D⟩ := PointedGroupFamily.Coefficients.pointed_group_coefficient_family_exists R ℂ X x₀ A m i a ha
  obtain ⟨B, p, hB, hp, hd⟩ := arithmetic_specialization_of_pointed_family X x₀ A a D n hn N hN
  exact ⟨D, B, p, hB, hp, hd⟩

end

end OAI.AlgebraicGeometry.PELModuli.IntegralModel.PointedFamilySpecialization.Coefficients

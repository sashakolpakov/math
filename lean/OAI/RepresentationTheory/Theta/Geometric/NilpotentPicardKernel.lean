import OAI.RepresentationTheory.Theta.Geometric.SquareZero.RelativeKernel
import OAI.RepresentationTheory.Theta.Geometric.NestedReductionMaps

/-! # Nilpotent Picard Kernel -/

namespace OAI.RepresentationTheory.Theta.Geometric.NilpotentPicardKernel

noncomputable section

/-! Successive square-zero reductions give triviality of the actual
relative Picard kernel over every nilpotent ideal. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj

theorem parameterPicardClass_kernel_restrict {A P T U : Over AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase} [GrpObj P]
    (Q : AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle (P ⊗ A).left) (r : T ⟶ P) (u : U ⟶ T)
    (h : ParameterizedPicardClass.parameterPicardClass Q r = ParameterizedPicardClass.parameterPicardClass Q (1 : T ⟶ P)) :
    ParameterizedPicardClass.parameterPicardClass Q (u ≫ r) = ParameterizedPicardClass.parameterPicardClass Q (1 : U ⟶ P) := by
  have H := (ParameterizedPicardClass.parameterPicardClass_naturality Q r u).symm.trans
    ((congrArg ((AlgebraicGeometry.AbelianModuli.HilbertConstruction.Picard.PicardSheaf.relativePicardSheaf A).obj.map u.op) h).trans
      (ParameterizedPicardClass.parameterPicardClass_naturality Q (1 : T ⟶ P) u))
  simpa using H

theorem affineTest_hom_eq_of_subsingleton {R : Type} [CommRing R] [Algebra ℂ R] [Subsingleton R]
    {P : Over AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase} (a b : AlgebraicGeometry.Foundations.Scheme.AffineComplexPoints.affineSchemeOver ℂ R ⟶ P) : a = b := by
  apply Over.OverMorphism.ext
  have : IsEmpty (AlgebraicGeometry.Foundations.Scheme.AffineComplexPoints.affineSchemeOver ℂ R).left := by
    refine ⟨fun p => ?_⟩
    have h1 : (1 : R) ∈ p.asIdeal := (Subsingleton.elim (0 : R) 1) ▸ p.asIdeal.zero_mem
    exact p.isPrime.ne_top (p.asIdeal.eq_top_of_isUnit_mem h1 isUnit_one)
  exact isInitialOfIsEmpty.hom_ext _ _

set_option backward.isDefEq.respectTransparency false in
theorem parameterPicardClass_nilpotent_relative_kernel
    {n : ℕ} (A : AlgebraicGeometry.AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme n AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase) {P : Over AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase} [GrpObj P]
    (Q : AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle (P ⊗ A.scheme).left)
    (eQ : (Q.pullback (lift (𝟙 P) (1 : P ⟶ A.scheme)).left).sheaf ≅ AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles.structureModule P.left)
    (hinj : Function.Injective (fun t : AlgebraicGeometry.AbelianModuli.ReferenceFamily.LieRanks.dualNumberTest ℂ ⟶ P => ParameterizedPicardClass.parameterPicardClass Q t))
    {R : Type} [CommRing R] [Algebra ℂ R] (I : Ideal R) (hI : IsNilpotent I)
    (r : AlgebraicGeometry.Foundations.Scheme.AffineComplexPoints.affineSchemeOver ℂ R ⟶ P) (hr : NestedReductionMaps.complexReductionMap I ≫ r = 1)
    (hQ : ParameterizedPicardClass.parameterPicardClass Q r = ParameterizedPicardClass.parameterPicardClass Q (1 : AlgebraicGeometry.Foundations.Scheme.AffineComplexPoints.affineSchemeOver ℂ R ⟶ P)) : r = 1 := by
  let property : ∀ {B : Type} [CommRing B], Ideal B → Prop := fun {B} _ J =>
    ∀ [Algebra ℂ B] (a : AlgebraicGeometry.Foundations.Scheme.AffineComplexPoints.affineSchemeOver ℂ B ⟶ P), NestedReductionMaps.complexReductionMap J ≫ a = 1 →
      ParameterizedPicardClass.parameterPicardClass Q a = ParameterizedPicardClass.parameterPicardClass Q (1 : AlgebraicGeometry.Foundations.Scheme.AffineComplexPoints.affineSchemeOver ℂ B ⟶ P) → a = 1
  have hall : property I := by
    apply Ideal.IsNilpotent.induction_on I hI
    · intro B _ J hJ _ a ha hQa
      rcases subsingleton_or_nontrivial B with hB | hB
      · let := hB
        exact affineTest_hom_eq_of_subsingleton a 1
      · let := hB
        exact SquareZero.RelativeKernel.parameterPicardClass_squareZero_relative_kernel J (by simpa only [pow_two] using hJ)
          A Q eQ hinj a ha hQa
    · intro B _ J K hJK hJ hK _ a ha hQa
      apply hJ a _ hQa
      apply hK (NestedReductionMaps.complexReductionMap J ≫ a) _ (parameterPicardClass_kernel_restrict Q a (NestedReductionMaps.complexReductionMap J) hQa)
      obtain ⟨w, hw⟩ := NestedReductionMaps.complexReductionMap_nested_factor J K hJK
      rw [← Category.assoc, hw, Category.assoc, ha]
      simp
  exact hall r hr hQ

end

end OAI.RepresentationTheory.Theta.Geometric.NilpotentPicardKernel

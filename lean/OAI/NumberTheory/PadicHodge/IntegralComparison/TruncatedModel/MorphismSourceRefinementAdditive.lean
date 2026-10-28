import OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.MorphismSourceRefinementCoordinates
import OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.MorphismGeometric
import OAI.NumberTheory.PadicHodge.IntegralComparison.Witt.RestrictedHomologyCoordinates
import OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.MorphismSourceRefinementEquality

/-! # Morphism Source Refinement Additive -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.MorphismSourceRefinementAdditive

noncomputable section

/-! The actual refinement from the small source cover to the common
source cover preserves the original additive crystalline comparison. -/
open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.HomologicalComplex
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

attribute [local irreducible] HomologicalComplex.homology HomologicalComplex.homologyMap

private theorem descend {C D : Type*} [Category* C] [Category* D]
    (F : C ⥤ D) {A B E : C} {T : D} (a : A ⟶ B) (e : B ≅ E) (m : A ⟶ E)
    (s : F.obj A ⟶ T) (t : F.obj B ⟶ T)
    (hm : a ≫ e.hom = m) (hs : s = F.map a ≫ t) :
    F.map m ≫ (F.map e.inv ≫ t) = s := by
  rw [← hm, F.map_comp]
  simp only [Category.assoc]
  rw [← Category.assoc (F.map e.hom) (F.map e.inv) t,
    ← F.map_comp e.hom e.inv, e.hom_inv_id, F.map_id, Category.id_comp]
  exact hs.symm

variable (p : ℕ) [Fact p.Prime] (k : Type) [Field k] [Fintype k] [CharP k p] (n : ℕ)
  {X₁ X₂ : Over (Spec (CommRingCat.of (Truncated.Witt.Ring p k n)))}
  [IsProper X₁.hom] [Smooth X₁.hom] [IsProper X₂.hom] [Smooth X₂.hom]
  [X₁.left.IsSeparated] [X₂.left.IsSeparated] (u : X₁ ⟶ X₂)
  {Y₁ : Over (Spec (CommRingCat.of k))} [IsSeparated Y₁.hom]
  (f₁ : Y₁.left ⟶ X₁.left)
  (hp₁ : IsPullback f₁ Y₁.hom X₁.hom
    (Spec.map (CommRingCat.ofHom (Truncated.Witt.reduction p k n))))
  (I₁ : InjectiveResolution (BoundedCrystalline.CrystallineCohomology.structureSheaf (p := p)
    (J := Ideal.span {(p : WittVector p k)}) (δ := AlgebraicGeometry.Crystalline.Cohomology.Witt.DividedPowers.WittDividedPowers.wittDividedPowers p k)
    (Witt.Crystalline.wittStructureMap p k Y₁) n))

private abbrev mapCore (q : ℕ) :=
  descend (homologyFunctor (ModuleCat (WittVector p k)) (.up ℕ) q ⋙
      SmoothWitt.DeRham.Comparison.coefficientFunctor p k)
    (MorphismIntrinsicCoordinates.Intrinsic.sourceMap p k n u)
    (MorphismCoverCoordinates.sourceIso p k n u)
    (((ModuleCat.restrictScalars
      (algebraMap (WittVector p k) (Truncated.Witt.Ring p k n))).mapHomologicalComplex
        (.up ℕ)).map (MorphismSourceRefinementCoordinates.map p k n u))
    (MorphismIntrinsicBase.IntrinsicComparison.sourceIso p k n f₁ hp₁ I₁ q).hom

private abbrev comparisonCore (q : ℕ) :=
  mapCore p k n u f₁ hp₁ I₁ q
    (MorphismIntrinsicBase.IntrinsicComparison.commonComparison p k n u f₁ hp₁ I₁ q)

private abbrev coordinatesCore (q : ℕ) :=
  comparisonCore p k n u f₁ hp₁ I₁ q
    (MorphismSourceRefinementCoordinates.coordinates p k n u)

theorem source_natural (q : ℕ) :
    MorphismSourceRefinementData.statement p k n u f₁ hp₁ I₁ q := by
  exact MorphismSourceRefinementEquality.comparison p k n u f₁ hp₁ I₁ q

abbrev homology (q : ℕ) :=
  coordinatesCore p k n u f₁ hp₁ I₁ q
    (source_natural p k n u f₁ hp₁ I₁ q)

abbrev coordinates_natural (q : ℕ) :=
  Witt.RestrictedHomologyCoordinates.inverse_natural p k
    (Truncated.Witt.Ring p k n)
    (MorphismSourceRefinementCoordinates.map p k n u) q

theorem comparison (q : ℕ)
    (x : (AlgebraicGeometry.Crystalline.Cohomology.Base.SmallDeRhamCech.BaseSmallDeRhamCech.total (Truncated.Witt.Ring p k n) X₁).homology q) :
    MorphismGeometric.TruncatedModelMorphismGeometricAdditive.comparison p k n u f₁ hp₁ I₁ q
      (homologyMap (MorphismSourceRefinementCoordinates.map p k n u) q x) =
    IntrinsicCohomology.Intrinsic.comparisonEquiv p k n X₁ Y₁ f₁ hp₁ I₁ q x := by
  exact (Witt.RestrictedHomologyCoordinates.comparison p k
    (Truncated.Witt.Ring p k n)
    (MorphismSourceRefinementCoordinates.map p k n u) q
    (MorphismGeometric.TruncatedModelMorphismGeometricHomology.comparison p k n u f₁ hp₁ I₁ q)
    (MorphismIntrinsicBase.IntrinsicComparison.sourceIso p k n f₁ hp₁ I₁ q).hom
    (MorphismSourceRefinementAdditive.homology p k n u f₁ hp₁ I₁ q) x).trans
      (Coordinates.Comparison.comparison_apply p k n X₁ Y₁ f₁ hp₁ I₁ q x).symm

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.MorphismSourceRefinementAdditive

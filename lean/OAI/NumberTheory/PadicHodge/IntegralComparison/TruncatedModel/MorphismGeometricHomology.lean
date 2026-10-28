import OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.MorphismGeometric
import OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.MorphismGeometricCoordinates
import OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.MorphismIntrinsic
import OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.MorphismTargetReferenceCoordinates

/-! # Morphism Geometric Homology -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.MorphismGeometricHomology

noncomputable section

/-! The literal geometric map to the common affine cover induces
the original bounded crystalline pullback. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

private theorem first_assoc {C : Type*} [Category* C] {A B D E F : C}
    (a : A ⟶ B) (b : B ⟶ D) (c : D ⟶ E) (d : E ⟶ F) (e : A ⟶ F)
    (h : a ≫ b ≫ c ≫ d = e) : (a ≫ b) ≫ c ≫ d = e :=
  (Category.assoc _ _ _).trans h

private theorem descend {C D : Type*} [Category* C] [Category* D]
    (F : C ⥤ D) {A B E L : C} {S T : D}
    (a : A ⟶ B) (b : B ⟶ E) (e : E ≅ L) (m : A ⟶ L)
    (c : F.obj E ⟶ S) (t : F.obj A ⟶ T) (g : T ⟶ S)
    (hm : a ≫ b ≫ e.hom = m) (hc : t ≫ g = F.map a ≫ F.map b ≫ c) :
    F.map m ≫ (F.map e.inv ≫ c) = t ≫ g := by
  rw [← hm, F.map_comp, F.map_comp]
  simp only [Category.assoc]
  rw [← Category.assoc (F.map e.hom) (F.map e.inv) c,
    ← F.map_comp e.hom e.inv, e.hom_inv_id, F.map_id, Category.id_comp]
  exact hc.symm

variable (p : ℕ) [Fact p.Prime] (k : Type) [Field k] [Fintype k] [CharP k p] (n : ℕ)
  {X₁ X₂ : Over (Spec (CommRingCat.of (Truncated.Witt.Ring p k n)))}
  [IsProper X₁.hom] [Smooth X₁.hom] [IsProper X₂.hom] [Smooth X₂.hom]
  [X₁.left.IsSeparated] [X₂.left.IsSeparated]
  {Y₁ Y₂ : Over (Spec (CommRingCat.of k))} [IsSeparated Y₁.hom] [IsSeparated Y₂.hom]
  (u : X₁ ⟶ X₂) (v : Y₁ ⟶ Y₂) (f₁ : Y₁.left ⟶ X₁.left) (f₂ : Y₂.left ⟶ X₂.left)
  (hp₁ : IsPullback f₁ Y₁.hom X₁.hom
    (Spec.map (CommRingCat.ofHom (Truncated.Witt.reduction p k n))))
  (hp₂ : IsPullback f₂ Y₂.hom X₂.hom
    (Spec.map (CommRingCat.ofHom (Truncated.Witt.reduction p k n))))
  (sq : f₁ ≫ u.left = v.left ≫ f₂)
  (I₁ : InjectiveResolution (BoundedCrystalline.CrystallineCohomology.structureSheaf (p := p)
    (J := Ideal.span {(p : WittVector p k)}) (δ := AlgebraicGeometry.Crystalline.Cohomology.Witt.DividedPowers.WittDividedPowers.wittDividedPowers p k)
    (Witt.Crystalline.wittStructureMap p k Y₁) n))
  (I₂ : InjectiveResolution (BoundedCrystalline.CrystallineCohomology.structureSheaf (p := p)
    (J := Ideal.span {(p : WittVector p k)}) (δ := AlgebraicGeometry.Crystalline.Cohomology.Witt.DividedPowers.WittDividedPowers.wittDividedPowers p k)
    (Witt.Crystalline.wittStructureMap p k Y₂) n))

abbrev total := first_assoc
  (OrdinaryCechCoordinates.Ordinary.iso p k n X₂).hom
  (MorphismOrdinaryCech.Ordinary.targetOrdinaryRefinement p k n u)
  (MorphismOrdinaryCech.Ordinary.ordinaryMap p k n u)
  (MorphismCoverCoordinates.sourceIso p k n u).hom
  ((((ModuleCat.restrictScalars (algebraMap (WittVector p k) (Truncated.Witt.Ring p k n)))).mapHomologicalComplex (.up ℕ)).map
    (MorphismGeometricCoordinates.map p k n u))
  (MorphismGeometricCoordinates.total p k n u)

abbrev naturality (i : ℕ) := descend
  (HomologicalComplex.homologyFunctor (ModuleCat (WittVector p k)) (.up ℕ) i ⋙ (SmoothWitt.DeRham.Comparison.coefficientFunctor p k))
  (MorphismIntrinsicCoordinates.Intrinsic.targetMap p k n u)
  (MorphismOrdinaryCech.Ordinary.ordinaryMap p k n u)
  (MorphismCoverCoordinates.sourceIso p k n u)
  ((((ModuleCat.restrictScalars (algebraMap (WittVector p k) (Truncated.Witt.Ring p k n)))).mapHomologicalComplex (.up ℕ)).map
    (MorphismGeometricCoordinates.map p k n u))
  (MorphismIntrinsicBase.IntrinsicComparison.commonComparison p k n u f₁ hp₁ I₁ i)
  (MorphismIntrinsicBase.IntrinsicComparison.targetIso p k n f₂ hp₂ I₂ i).hom
  (ModuleCat.ofHom (BoundedCrystalline.CrystallinePullback.pullback v.left
    (MorphismData.Frames.ambient_over p k v) n i))
  (total p k n u)
  (MorphismTargetReferenceCoordinates.Reference.target p k n u v f₁ f₂ hp₁ hp₂ sq I₁ I₂ i)

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.MorphismGeometricHomology

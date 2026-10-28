import OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.SheafHomologyData

/-! # Sheaf Ordered -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.SheafOrdered.Comparison

noncomputable section

/-! The actual sheaf comparison into the ordered small-cover total is
identified by the original bounded crystalline comparison and its
canonical global-section edge. -/
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry _root_.HomologicalComplex
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

private theorem ordered_paste
    (p : ℕ) [Fact p.Prime] (k : Type) [Field k] [Fintype k] [CharP k p]
    (n : ℕ) (X : Over (Spec (CommRingCat.of (Truncated.Witt.Ring p k n))))
    [IsProper X.hom] [Smooth X.hom] [X.left.IsSeparated]
    (K L : CochainComplex (X.left.Opensᵒᵖ ⥤
      ModuleCat.{2} (Crystalline.ExactRestriction.Coeff (B := WittVector p k))) ℕ)
    (q : ℕ) (a : K ⟶ L)
    {A B C : ModuleCat.{2} (Crystalline.ExactRestriction.Coeff (B := WittVector p k))}
    (native : A ⟶ (IntrinsicConeCoordinates.Intrinsic.ordinaryTotal p k n X K).homology q)
    (comparison : A ⟶ B) (inverse : B ⟶ C)
    (product : C ⟶ (IntrinsicConeCoordinates.Intrinsic.ordinaryTotal p k n X L).homology q)
    (edge : B ⟶ ((OrderedCech.TotalProjection.ordered
      (AlgebraicGeometry.Crystalline.Cohomology.Base.SmallDeRhamCech.BaseSmallDeRhamCech.opens (Truncated.Witt.Ring p k n) X)).obj L).homology q)
    (hordinary : native ≫ homologyMap (SheafHomologyData.OrderedComparison.Typed.ordinaryMap p k n X a) q =
        comparison ≫ inverse ≫ product)
    (hsmall : inverse ≫ product ≫ homologyMap (OrderedCech.TotalProjection.map
      (AlgebraicGeometry.Crystalline.Cohomology.Base.SmallDeRhamCech.BaseSmallDeRhamCech.opens (Truncated.Witt.Ring p k n) X) L) q = edge) :
    native ≫ homologyMap (OrderedCech.TotalProjection.map
      (AlgebraicGeometry.Crystalline.Cohomology.Base.SmallDeRhamCech.BaseSmallDeRhamCech.opens (Truncated.Witt.Ring p k n) X) K) q ≫
      homologyMap ((OrderedCech.TotalProjection.ordered
        (AlgebraicGeometry.Crystalline.Cohomology.Base.SmallDeRhamCech.BaseSmallDeRhamCech.opens (Truncated.Witt.Ring p k n) X)).map a) q =
    comparison ≫ edge := by
  have hn :
      homologyMap (SheafHomologyData.OrderedComparison.Typed.ordinaryMap p k n X a) q ≫
        homologyMap (OrderedCech.TotalProjection.map
          (AlgebraicGeometry.Crystalline.Cohomology.Base.SmallDeRhamCech.BaseSmallDeRhamCech.opens (Truncated.Witt.Ring p k n) X) L) q =
      homologyMap (OrderedCech.TotalProjection.map
        (AlgebraicGeometry.Crystalline.Cohomology.Base.SmallDeRhamCech.BaseSmallDeRhamCech.opens (Truncated.Witt.Ring p k n) X) K) q ≫
        homologyMap ((OrderedCech.TotalProjection.ordered
          (AlgebraicGeometry.Crystalline.Cohomology.Base.SmallDeRhamCech.BaseSmallDeRhamCech.opens (Truncated.Witt.Ring p k n) X)).map a) q :=
    OrderedCech.TotalProjection.homology_naturality
      (AlgebraicGeometry.Crystalline.Cohomology.Base.SmallDeRhamCech.BaseSmallDeRhamCech.opens (Truncated.Witt.Ring p k n) X) a q
  rw [← hn, ← Category.assoc, hordinary]
  simp only [Category.assoc]
  rw [hsmall]

private theorem apply_ordered
    (p : ℕ) [Fact p.Prime] (k : Type) [Field k]
    {A B C D E : ModuleCat.{2} (Crystalline.ExactRestriction.Coeff (B := WittVector p k))}
    (a : A ⟶ B) (b : B ⟶ C) (c : C ⟶ D) (f : A ⟶ E) (edge : E ⟶ D)
    (h : a ≫ b ≫ c = f ≫ edge) (x : A) (y : E) (hy : y = f x) :
    c (b (a x)) = edge y := by
  rw [hy]
  exact ConcreteCategory.congr_hom h x

variable (p : ℕ) [Fact p.Prime] (k : Type) [Field k] [Fintype k] [CharP k p]
  (n : ℕ) (X : Over (Spec (CommRingCat.of (Truncated.Witt.Ring p k n))))
  [IsProper X.hom] [Smooth X.hom] [X.left.IsSeparated]
  (Y : Over (Spec (CommRingCat.of k))) [IsSeparated Y.hom] (f : Y.left ⟶ X.left)
  (hp : IsPullback f Y.hom X.hom
    (Spec.map (CommRingCat.ofHom (Truncated.Witt.reduction p k n))))
  (I : InjectiveResolution (BoundedCrystalline.CrystallineCohomology.structureSheaf (p := p)
    (J := Ideal.span {(p : WittVector p k)}) (δ := AlgebraicGeometry.Crystalline.Cohomology.Witt.DividedPowers.WittDividedPowers.wittDividedPowers p k)
    (Witt.Crystalline.wittStructureMap p k Y) n))

abbrev ordered_homology (q : ℕ) :=
  ordered_paste p k n X (SheafProduct.OrderedComparison.source p k n X) (SheafProduct.OrderedComparison.target p k n X Y f I) q
    (SheafProduct.OrderedComparison.map p k n X Y f hp I)
    (homologyMap (SheafHomologyData.OrderedComparison.Typed.nativeCoordinates p k n X) q)
    (GlobalDeRham.Comparison.homologyIso p k n X Y f hp I q).hom
    (ResolutionIntrinsicHomology.Intrinsic.iso p k n X Y f I q).inv
    (homologyMap (ResolutionGlobal.smallProductIso p k n X Y f I).hom q)
    (CechIso.ResolutionGlobal.toOrdered p k n X Y f I
      (AlgebraicGeometry.Crystalline.Cohomology.Base.SmallDeRhamCech.BaseSmallDeRhamCech.opens (Truncated.Witt.Ring p k n) X) q)
    (SheafHomologyData.OrderedComparison.ordinary_homology p k n X Y f hp I q)
    (ModelResolutionGlobal.small_homology p k n X Y f I q)

theorem ordered_apply (q : ℕ)
    (x : (AlgebraicGeometry.Crystalline.Cohomology.Base.SmallDeRhamCech.BaseSmallDeRhamCech.total (Truncated.Witt.Ring p k n) X).homology q) :
    homologyMap (SheafProduct.OrderedComparison.orderedMap p k n X Y f hp I) q
      (homologyMap (OrderedCech.TotalProjection.map
        (AlgebraicGeometry.Crystalline.Cohomology.Base.SmallDeRhamCech.BaseSmallDeRhamCech.opens (Truncated.Witt.Ring p k n) X) (SheafProduct.OrderedComparison.source p k n X)) q
        (homologyMap (SheafSourceCoordinates.nativeCoordinates p k n X).hom q
          (Intrinsic.inputEquiv p k n X q x))) =
    CechIso.ResolutionGlobal.toOrdered p k n X Y f I
      (AlgebraicGeometry.Crystalline.Cohomology.Base.SmallDeRhamCech.BaseSmallDeRhamCech.opens (Truncated.Witt.Ring p k n) X) q
      (IntrinsicCohomology.Intrinsic.comparisonEquiv p k n X Y f hp I q x) :=

  apply_ordered p k
    (homologyMap (SheafHomologyData.OrderedComparison.Typed.nativeCoordinates p k n X) q)
    (homologyMap (OrderedCech.TotalProjection.map
      (AlgebraicGeometry.Crystalline.Cohomology.Base.SmallDeRhamCech.BaseSmallDeRhamCech.opens (Truncated.Witt.Ring p k n) X) (SheafProduct.OrderedComparison.source p k n X)) q)
    (homologyMap (SheafProduct.OrderedComparison.orderedMap p k n X Y f hp I) q)
    (GlobalDeRham.Comparison.homologyIso p k n X Y f hp I q).hom
    (CechIso.ResolutionGlobal.toOrdered p k n X Y f I
      (AlgebraicGeometry.Crystalline.Cohomology.Base.SmallDeRhamCech.BaseSmallDeRhamCech.opens (Truncated.Witt.Ring p k n) X) q)
    (ordered_homology p k n X Y f hp I q)
    (Intrinsic.inputEquiv p k n X q x)
    (IntrinsicCohomology.Intrinsic.comparisonEquiv p k n X Y f hp I q x)
    (Intrinsic.comparison p k n X Y f hp I q x)

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.SheafOrdered.Comparison

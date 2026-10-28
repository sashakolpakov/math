import OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.ResolutionGlobal

/-! # Model Resolution Global -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.ModelResolutionGlobal

noncomputable section

/-! The original bounded crystalline comparison gives the global
ordered edge through explicit native small-cover cone coordinates. -/
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry Opposite _root_.HomologicalComplex
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

private theorem homology_composite {C : Type*} [Category C] [HasZeroMorphisms C]
    {R A B T : CochainComplex C ℕ} (q : ℕ)
    [R.HasHomology q] [A.HasHomology q] [B.HasHomology q] [T.HasHomology q]
    {c c' : R ⟶ A} {a : A ⟶ B} {b : B ⟶ T} {o : R ⟶ T}
    (hc : c = c') (h : (c' ≫ a) ≫ b = o) :
    (homologyMap c q ≫ homologyMap a q) ≫ homologyMap b q = homologyMap o q := by
  rw [hc]
  calc
    _ = homologyMap ((c' ≫ a) ≫ b) q := by simp only [homologyMap_comp]
    _ = homologyMap o q := congrArg (fun m => homologyMap m q) h

private theorem inverse_edge {C : Type*} [Category C] {A B D E F : C}
    (e : B ≅ D) (g : A ≅ D) (a : A ⟶ B) (p : B ⟶ E) (o : A ⟶ E)
    (π : E ⟶ F) (edge : A ⟶ F)
    (hg : a ≫ e.hom = g.hom) (hp : a ≫ p = o) (ho : o ≫ π = edge) :
    e.inv ≫ p ≫ π = g.inv ≫ edge := by
  apply (cancel_epi g.hom).mp
  calc
    g.hom ≫ (e.inv ≫ p ≫ π) = a ≫ p ≫ π := by
      rw [← hg]
      simp only [Category.assoc, Iso.hom_inv_id_assoc]
    _ = edge := by rw [← Category.assoc, hp, ho]
    _ = g.hom ≫ (g.inv ≫ edge) := by simp only [Iso.hom_inv_id_assoc]

private theorem ordinary_homology_composite
    (p : ℕ) [Fact p.Prime] (k : Type) [Field k] [Fintype k] [CharP k p]
    (n : ℕ) (X : Over (Spec (CommRingCat.of (Truncated.Witt.Ring p k n))))
    [IsProper X.hom] [Smooth X.hom] [X.left.IsSeparated]
    (K : CochainComplex (X.left.Opensᵒᵖ ⥤
      ModuleCat.{2} (Crystalline.ExactRestriction.Coeff (B := WittVector p k))) ℕ)
    (q : ℕ)
    {A B : CochainComplex
      (ModuleCat.{2} (Crystalline.ExactRestriction.Coeff (B := WittVector p k))) ℕ}
    {c c' : Presheaf.OrderedCechEdge.sections K ⟶ A}
    {a : A ⟶ B}
    {b : B ⟶ IntrinsicConeCoordinates.Intrinsic.ordinaryTotal p k n X K}
    (hc : c = c')
    (h : (c' ≫ a) ≫ b =
      ResolutionGlobal.CochainSquare.Typed.ordinary p k n X K) :
    (homologyMap c q ≫ homologyMap a q) ≫ homologyMap b q =
      homologyMap (Presheaf.OrdinaryOrderedEdge.Ordinary.ordinary
        (AlgebraicGeometry.Crystalline.Cohomology.Base.SmallDeRhamCech.BaseSmallDeRhamCech.opens (Truncated.Witt.Ring p k n) X) K) q :=
  (homology_composite q hc h).trans
    (ResolutionGlobal.CochainSquare.Typed.homology p k n X K q)

private theorem ordered_inverse
    (p : ℕ) [Fact p.Prime] (k : Type) [Field k] [Fintype k] [CharP k p]
    (n : ℕ) (X : Over (Spec (CommRingCat.of (Truncated.Witt.Ring p k n))))
    [IsProper X.hom] [Smooth X.hom] [X.left.IsSeparated]
    (K : CochainComplex (X.left.Opensᵒᵖ ⥤
      ModuleCat.{2} (Crystalline.ExactRestriction.Coeff (B := WittVector p k))) ℕ)
    (q : ℕ)
    {B D : ModuleCat.{2} (Crystalline.ExactRestriction.Coeff (B := WittVector p k))}
    (e : B ≅ D) (g : (Presheaf.OrderedCechEdge.sections K).homology q ≅ D)
    (a : (Presheaf.OrderedCechEdge.sections K).homology q ⟶ B)
    (b : B ⟶ (IntrinsicConeCoordinates.Intrinsic.ordinaryTotal p k n X K).homology q)
    (hg : a ≫ e.hom = g.hom)
    (hp : a ≫ b = homologyMap (Presheaf.OrdinaryOrderedEdge.Ordinary.ordinary
      (AlgebraicGeometry.Crystalline.Cohomology.Base.SmallDeRhamCech.BaseSmallDeRhamCech.opens (Truncated.Witt.Ring p k n) X) K) q) :
    e.inv ≫ b ≫ homologyMap (OrderedCech.TotalProjection.map
      (AlgebraicGeometry.Crystalline.Cohomology.Base.SmallDeRhamCech.BaseSmallDeRhamCech.opens (Truncated.Witt.Ring p k n) X) K) q =
    g.inv ≫ homologyMap (Presheaf.OrderedCechEdge.edge
      (AlgebraicGeometry.Crystalline.Cohomology.Base.SmallDeRhamCech.BaseSmallDeRhamCech.opens (Truncated.Witt.Ring p k n) X) K) q :=
  inverse_edge
    (C := ModuleCat.{2} (Crystalline.ExactRestriction.Coeff (B := WittVector p k)))
    e g a b
    (homologyMap (Presheaf.OrdinaryOrderedEdge.Ordinary.ordinary
      (AlgebraicGeometry.Crystalline.Cohomology.Base.SmallDeRhamCech.BaseSmallDeRhamCech.opens (Truncated.Witt.Ring p k n) X) K) q)
    (homologyMap (OrderedCech.TotalProjection.map
      (AlgebraicGeometry.Crystalline.Cohomology.Base.SmallDeRhamCech.BaseSmallDeRhamCech.opens (Truncated.Witt.Ring p k n) X) K) q)
    (homologyMap (Presheaf.OrderedCechEdge.edge
      (AlgebraicGeometry.Crystalline.Cohomology.Base.SmallDeRhamCech.BaseSmallDeRhamCech.opens (Truncated.Witt.Ring p k n) X) K) q)
    hg hp
    (Presheaf.OrdinaryOrderedEdge.Ordinary.homology
      (AlgebraicGeometry.Crystalline.Cohomology.Base.SmallDeRhamCech.BaseSmallDeRhamCech.opens (Truncated.Witt.Ring p k n) X) K q)

variable (p : ℕ) [Fact p.Prime] (k : Type) [Field k] [Fintype k] [CharP k p]
  (n : ℕ) (X : Over (Spec (CommRingCat.of (Truncated.Witt.Ring p k n))))
  [IsProper X.hom] [Smooth X.hom] [X.left.IsSeparated]
  (Y : Over (Spec (CommRingCat.of k))) [IsSeparated Y.hom] (f : Y.left ⟶ X.left)
  (I : InjectiveResolution (BoundedCrystalline.CrystallineCohomology.structureSheaf (p := p)
    (J := Ideal.span {(p : WittVector p k)}) (δ := AlgebraicGeometry.Crystalline.Cohomology.Witt.DividedPowers.WittDividedPowers.wittDividedPowers p k)
    (Witt.Crystalline.wittStructureMap p k Y) n))

attribute [local irreducible] HomologicalComplex.homology CechIso.ResolutionGlobal.globalIso ResolutionGlobal.nativeGlobalIso ResolutionGlobal.nativeEdge ResolutionGlobal.smallProductIso

omit [IsSeparated Y.hom] in
theorem small_product_homology (q : ℕ) :
    (homologyMap (CechIso.ResolutionGlobal.globalIso p k n X Y f I).hom q ≫
      homologyMap (ResolutionGlobal.nativeEdge p k n X Y f I) q) ≫
      homologyMap (ResolutionGlobal.smallProductIso p k n X Y f I).hom q =
    homologyMap (Presheaf.OrdinaryOrderedEdge.Ordinary.ordinary
      (AlgebraicGeometry.Crystalline.Cohomology.Base.SmallDeRhamCech.BaseSmallDeRhamCech.opens (Truncated.Witt.Ring p k n) X)
      (CechIso.ResolutionGlobal.presheaf p k n X Y f I)) q :=
  ordinary_homology_composite p k n X (CechIso.ResolutionGlobal.presheaf p k n X Y f I) q
    (ResolutionGlobal.global_coordinate p k n X Y f I)
    (ResolutionGlobal.CochainSquare.comparison p k n X Y f I)

omit [IsSeparated Y.hom] in
theorem small_homology (q : ℕ) :
    (ResolutionIntrinsicHomology.Intrinsic.iso p k n X Y f I q).inv ≫
      homologyMap (ResolutionGlobal.smallProductIso p k n X Y f I).hom q ≫
      homologyMap (OrderedCech.TotalProjection.map
        (AlgebraicGeometry.Crystalline.Cohomology.Base.SmallDeRhamCech.BaseSmallDeRhamCech.opens (Truncated.Witt.Ring p k n) X) (CechIso.ResolutionGlobal.presheaf p k n X Y f I)) q =
    CechIso.ResolutionGlobal.toOrdered p k n X Y f I (AlgebraicGeometry.Crystalline.Cohomology.Base.SmallDeRhamCech.BaseSmallDeRhamCech.opens (Truncated.Witt.Ring p k n) X) q :=
  ordered_inverse p k n X (CechIso.ResolutionGlobal.presheaf p k n X Y f I) q
    (ResolutionIntrinsicHomology.Intrinsic.iso p k n X Y f I q)
    (CechIso.ResolutionGlobal.globalHomologyIso p k n X Y f I q)
    (homologyMap (CechIso.ResolutionGlobal.globalIso p k n X Y f I).hom q ≫ homologyMap (ResolutionGlobal.nativeEdge p k n X Y f I) q)
    (homologyMap (ResolutionGlobal.smallProductIso p k n X Y f I).hom q)
    (ResolutionGlobal.small_global_homology p k n X Y f I q) (small_product_homology p k n X Y f I q)

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.ModelResolutionGlobal

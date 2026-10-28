import OAI.NumberTheory.PadicHodge.IntegralComparison.IntrinsicDeRham.TopEdgeTransfer

/-! # Top Form Transfer Degree -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Intrinsic.TopFormTransferDegree

noncomputable section

/-! On the original top-form Čech cohomology, finite étale pullback
followed by transfer is multiplication by the actual finite-flat rank. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

private theorem conjugate {C : Type*} [Category C] [Preadditive C]
    {A B K L : C} (e : A ≅ K) (s : B ≅ L) (f : K ⟶ L) (g : L ⟶ K)
    (d : ℕ) (h : f ≫ g = d • 𝟙 K) :
    (e.hom ≫ f ≫ s.inv) ≫ (s.hom ≫ g ≫ e.inv) = d • 𝟙 A := by
  simp only [Category.assoc, Iso.inv_hom_id_assoc]
  rw [← Category.assoc f, h]
  simp only [Preadditive.nsmul_comp, Preadditive.comp_nsmul,
    Category.id_comp, Iso.hom_inv_id]

private theorem homology_scalar {C : Type*} [Category C] [Abelian C]
    {K L : CochainComplex C ℕ} (f : K ⟶ L) (g : L ⟶ K) (d q : ℕ)
    (h : f ≫ g = d • 𝟙 K) :
    HomologicalComplex.homologyMap f q ≫ HomologicalComplex.homologyMap g q =
      d • 𝟙 (K.homology q) := by
  change (HomologicalComplex.homologyFunctor C (.up ℕ) q).map f ≫
    (HomologicalComplex.homologyFunctor C (.up ℕ) q).map g = _
  rw [← Functor.map_comp, h, Functor.map_nsmul, CategoryTheory.Functor.map_id]
  rfl

universe u
variable (R : Type u) [CommRing R]
  (X Y : Over (Spec (CommRingCat.of R))) (f : X ⟶ Y)
  [IsFinite f.left] [Etale f.left]
  {ι : Type u} (U : ι → Y.left.Opens) (g : ℕ)
  [SmoothOfRelativeDimension g X.hom] [IsProper X.hom]
  [SmoothOfRelativeDimension g Y.hom] [IsProper Y.hom]
  [PreconnectedSpace Y.left]

omit [SmoothOfRelativeDimension g X.hom] [IsProper X.hom] in
theorem pullback_trace (y : Y.left) (x : IntrinsicDeRham.TopEdge.Intrinsic.source R Y U g) :
    IntrinsicDeRham.TopEdgeTransfer.Intrinsic.trace R X Y f U g
      (IntrinsicDeRham.TopEdgeTransfer.Intrinsic.pullback R X Y f U g x) = f.left.finrank y • x := by
  let : Smooth Y.hom := SmoothOfRelativeDimension.smooth g Y.hom
  let V := IntrinsicDeRham.CechTransfer.Intrinsic.inverseCover R X Y f U
  let a := (IntrinsicDeRham.CechTransfer.Intrinsic.pullback R X Y f U).f g
  let b := (IntrinsicDeRham.CechTransfer.Intrinsic.trace R X Y f U).f g
  have hrow : a ≫ b = f.left.finrank y • 𝟙 ((IntrinsicDeRham.CechComplex.Intrinsic.bicomplex R Y U).X g) :=
    congrArg (fun c => c.f g) (IntrinsicDeRham.CechTransfer.Intrinsic.pullback_trace R X Y f U y)
  have h := conjugate
    (HomologicalComplex.homologyMapIso (IntrinsicDeRham.TopEdge.Intrinsic.rowIso R Y U g) g)
    (HomologicalComplex.homologyMapIso (IntrinsicDeRham.TopEdge.Intrinsic.rowIso R X V g) g)
    (HomologicalComplex.homologyMap a g) (HomologicalComplex.homologyMap b g)
    (f.left.finrank y) (homology_scalar a b (f.left.finrank y) g hrow)
  exact ConcreteCategory.congr_hom h x

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Intrinsic.TopFormTransferDegree

import OAI.NumberTheory.PadicHodge.GeometricComparison.Intrinsic.ExtensionAdapter

/-! # Extension Composition -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.ExtensionComposition.FormsAdapter

noncomputable section

section

/-! Extension by zero preserves composition of pullbacks across canonically compared functors. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits

variable {C D E : Type*} [Category* C] [Category* D] [Category* E]
  [Preadditive C] [Preadditive D] [Preadditive E]
  [HasZeroObject C] [HasZeroObject D] [HasZeroObject E]
  (F : C ⥤ D) (G : D ⥤ E) (H : C ⥤ E) [F.Additive] [G.Additive] [H.Additive]
  (e : F ⋙ G ≅ H)
  {K : CochainComplex C ℕ} {L : CochainComplex D ℕ} {M : CochainComplex E ℕ}
  (a : (F.mapHomologicalComplex (ComplexShape.up ℕ)).obj K ⟶ L)
  (b : (G.mapHomologicalComplex (ComplexShape.up ℕ)).obj L ⟶ M)
  (c : (H.mapHomologicalComplex (ComplexShape.up ℕ)).obj K ⟶ M)

theorem extendedMapX_comp
    (h : ∀ n, G.map (a.f n) ≫ b.f n = e.hom.app (K.X n) ≫ c.f n) (o : Option ℕ) :
    G.map ((AlgebraicGeometry.Comparison.Betti.Complex.Extension.mapXIso F K o).hom ≫ HomologicalComplex.extend.mapX a o) ≫
        ((AlgebraicGeometry.Comparison.Betti.Complex.Extension.mapXIso G L o).hom ≫ HomologicalComplex.extend.mapX b o) =
      e.hom.app (HomologicalComplex.extend.X K o) ≫
        ((AlgebraicGeometry.Comparison.Betti.Complex.Extension.mapXIso H K o).hom ≫ HomologicalComplex.extend.mapX c o) := by
  cases o with
  | none => exact (isZero_zero E).eq_of_tgt _ _
  | some n =>
    change G.map (𝟙 _ ≫ a.f n) ≫ (𝟙 _ ≫ b.f n) = e.hom.app _ ≫ (𝟙 _ ≫ c.f n)
    exact (congrArg (fun u => G.map u ≫ (𝟙 _ ≫ b.f n)) (Category.id_comp (a.f n))).trans
      ((congrArg (fun u => G.map (a.f n) ≫ u) (Category.id_comp (b.f n))).trans
        ((h n).trans (congrArg (fun u => e.hom.app (K.X n) ≫ u) (Category.id_comp (c.f n)).symm)))

theorem extendedPullback_comp (ι : (ComplexShape.up ℕ).Embedding (ComplexShape.up ℤ))
    (h : (G.mapHomologicalComplex (ComplexShape.up ℕ)).map a ≫ b =
      (NatTrans.mapHomologicalComplex e.hom (ComplexShape.up ℕ)).app K ≫ c) :
    (G.mapHomologicalComplex (ComplexShape.up ℤ)).map (Intrinsic.ExtensionAdapter.FormsAdapter.extendedPullback F ι a) ≫
        Intrinsic.ExtensionAdapter.FormsAdapter.extendedPullback G ι b =
      (NatTrans.mapHomologicalComplex e.hom (ComplexShape.up ℤ)).app (K.extend ι) ≫
        Intrinsic.ExtensionAdapter.FormsAdapter.extendedPullback H ι c := by
  apply HomologicalComplex.Hom.ext
  funext i
  exact extendedMapX_comp F G H e a b c (fun n => congrArg (fun m => m.f n) h) (ι.r i)

end

/-! Extension by zero preserves squares of the specified coefficient and pullback maps. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits

theorem padded_square {B C D : Type*} [Category* B] [Category* C] [Category* D]
    (G : B ⥤ D) (J : C ⥤ D) {b b' : B} {c c' : C} {d : D}
    (e : G.obj b ⟶ J.obj c) (a : b ⟶ b') (v : G.obj b' ⟶ d)
    (h : c ⟶ c') (j : J.obj c' ⟶ d)
    (hs : G.map a ≫ v = e ≫ J.map h ≫ j) :
    G.map (𝟙 b ≫ a) ≫ (𝟙 (G.obj b') ≫ v) =
      e ≫ J.map (𝟙 c ≫ h) ≫ (𝟙 (J.obj c') ≫ j) := by
  simpa only [Category.id_comp] using hs

variable {A B C D : Type*} [Category* A] [Category* B] [Category* C] [Category* D]
  [Preadditive A] [Preadditive B] [Preadditive C] [Preadditive D]
  [HasZeroObject A] [HasZeroObject B] [HasZeroObject C] [HasZeroObject D]
  (F : A ⥤ B) (G : B ⥤ D) (H : A ⥤ C) (J : C ⥤ D)
  [F.Additive] [G.Additive] [H.Additive] [J.Additive] (e : F ⋙ G ≅ H ⋙ J)
  {K : CochainComplex A ℕ} {L : CochainComplex B ℕ}
  {N : CochainComplex C ℕ} {M : CochainComplex D ℕ}
  (a : (F.mapHomologicalComplex (ComplexShape.up ℕ)).obj K ⟶ L)
  (b : (G.mapHomologicalComplex (ComplexShape.up ℕ)).obj L ⟶ M)
  (c : (H.mapHomologicalComplex (ComplexShape.up ℕ)).obj K ⟶ N)
  (d : (J.mapHomologicalComplex (ComplexShape.up ℕ)).obj N ⟶ M)

theorem extendedMapX_square
    (h : ∀ n, G.map (a.f n) ≫ b.f n = e.hom.app (K.X n) ≫ J.map (c.f n) ≫ d.f n)
    (o : Option ℕ) :
    G.map ((AlgebraicGeometry.Comparison.Betti.Complex.Extension.mapXIso F K o).hom ≫ HomologicalComplex.extend.mapX a o) ≫
        ((AlgebraicGeometry.Comparison.Betti.Complex.Extension.mapXIso G L o).hom ≫ HomologicalComplex.extend.mapX b o) =
      e.hom.app (HomologicalComplex.extend.X K o) ≫
        J.map ((AlgebraicGeometry.Comparison.Betti.Complex.Extension.mapXIso H K o).hom ≫ HomologicalComplex.extend.mapX c o) ≫
          ((AlgebraicGeometry.Comparison.Betti.Complex.Extension.mapXIso J N o).hom ≫ HomologicalComplex.extend.mapX d o) := by
  cases o with
  | none => exact (isZero_zero D).eq_of_tgt _ _
  | some n =>
    exact padded_square G J (e.hom.app (K.X n)) (a.f n) (b.f n) (c.f n) (d.f n) (h n)

theorem extendedFourFunctor_square (ι : (ComplexShape.up ℕ).Embedding (ComplexShape.up ℤ))
    (h : (G.mapHomologicalComplex (ComplexShape.up ℕ)).map a ≫ b =
      (NatTrans.mapHomologicalComplex e.hom (ComplexShape.up ℕ)).app K ≫
        (J.mapHomologicalComplex (ComplexShape.up ℕ)).map c ≫ d) :
    (G.mapHomologicalComplex (ComplexShape.up ℤ)).map (Intrinsic.ExtensionAdapter.FormsAdapter.extendedPullback F ι a) ≫
        Intrinsic.ExtensionAdapter.FormsAdapter.extendedPullback G ι b =
      (NatTrans.mapHomologicalComplex e.hom (ComplexShape.up ℤ)).app (K.extend ι) ≫
        (J.mapHomologicalComplex (ComplexShape.up ℤ)).map (Intrinsic.ExtensionAdapter.FormsAdapter.extendedPullback H ι c) ≫
          Intrinsic.ExtensionAdapter.FormsAdapter.extendedPullback J ι d := by
  apply HomologicalComplex.Hom.ext
  funext i
  exact extendedMapX_square F G H J e a b c d (fun n => congrArg (fun m => m.f n) h) (ι.r i)

end

end OAI.NumberTheory.PadicHodge.GeometricComparison.ExtensionComposition.FormsAdapter

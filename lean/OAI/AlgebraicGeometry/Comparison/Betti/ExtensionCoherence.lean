import OAI.AlgebraicGeometry.Comparison.Betti.Complex.Extension

/-! # Extension Coherence -/

namespace OAI.AlgebraicGeometry.Comparison.Betti.ExtensionCoherence.Complex

noncomputable section

/-! Coherence of the canonical extension isomorphisms for additive functors. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits

open _root_.Complex

variable {C D E : Type*} [Category* C] [Category* D] [Category* E]
  [Preadditive C] [Preadditive D] [Preadditive E]
  [HasZeroObject C] [HasZeroObject D] [HasZeroObject E]
  (F : C ⥤ D) (G : D ⥤ E) [F.Additive] [G.Additive]
  {ι ι' : Type*} {c : ComplexShape ι} {c' : ComplexShape ι'}

theorem mapXIso_inv_naturality {K L : HomologicalComplex C c} (φ : K ⟶ L) (o : Option ι) :
    (Complex.Extension.mapXIso F K o).inv ≫ F.map (HomologicalComplex.extend.mapX φ o) =
      HomologicalComplex.extend.mapX ((F.mapHomologicalComplex c).map φ) o ≫
        (Complex.Extension.mapXIso F L o).inv := by
  cases o with
  | none => exact (isZero_zero D).eq_of_src _ _
  | some i =>
    change 𝟙 _ ≫ F.map (φ.f i) = F.map (φ.f i) ≫ 𝟙 _
    simp only [Category.id_comp, Category.comp_id]

theorem mapExtendIso_inv_naturality (e : c.Embedding c')
    {K L : HomologicalComplex C c} (φ : K ⟶ L) :
    (Complex.Extension.mapExtendIso F e K).inv ≫
        (F.mapHomologicalComplex c').map (HomologicalComplex.extendMap φ e) =
      HomologicalComplex.extendMap ((F.mapHomologicalComplex c).map φ) e ≫
        (Complex.Extension.mapExtendIso F e L).inv := by
  apply HomologicalComplex.Hom.ext
  funext i
  exact mapXIso_inv_naturality F φ (e.r i)

theorem mapXIso_comp_inv (K : HomologicalComplex C c) (o : Option ι) :
    (Complex.Extension.mapXIso G ((F.mapHomologicalComplex c).obj K) o).inv ≫ G.map (Complex.Extension.mapXIso F K o).inv =
      (Complex.Extension.mapXIso (F ⋙ G) K o).inv := by
  cases o with
  | none => exact (isZero_zero E).eq_of_src _ _
  | some i =>
    change 𝟙 _ ≫ G.map (𝟙 (F.obj (K.X i))) = 𝟙 _
    rw [G.map_id, Category.id_comp]

theorem mapExtendIso_comp_inv (e : c.Embedding c') (K : HomologicalComplex C c) :
    (Complex.Extension.mapExtendIso G e ((F.mapHomologicalComplex c).obj K)).inv ≫
        (G.mapHomologicalComplex c').map (Complex.Extension.mapExtendIso F e K).inv =
      (Complex.Extension.mapExtendIso (F ⋙ G) e K).inv := by
  apply HomologicalComplex.Hom.ext
  funext i
  exact mapXIso_comp_inv F G K (e.r i)

end

end OAI.AlgebraicGeometry.Comparison.Betti.ExtensionCoherence.Complex

import OAI.Algebra.Homology.MapExtend

/-! # Map Extend Composition -/

namespace OAI.AlgebraicGeometry.ComplexMultiplication.MapExtendComposition

noncomputable section

/-! # The original mapping/extension comparison respects composite functors -/

open _root_.CategoryTheory Limits

variable {C D E : Type*} [Category* C] [Category* D] [Category* E]
  [Preadditive C] [Preadditive D] [Preadditive E]
  [HasZeroObject C] [HasZeroObject D] [HasZeroObject E]
  (F : C ⥤ D) (G : D ⥤ E) [F.Additive] [G.Additive]
  {I J : Type*} {c : ComplexShape I} {c' : ComplexShape J}

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- The actual canonical comparison for a composite is the composite of the comparisons. -/
theorem mapExtendCanonicalIso_comp (K : HomologicalComplex C c) (e : c.Embedding c') :
    (Algebra.Homology.MapExtend.HomologicalComplex.mapExtendCanonicalIso (F ⋙ G) K e).hom =
      (G.mapHomologicalComplex c').map
          (Algebra.Homology.MapExtend.HomologicalComplex.mapExtendCanonicalIso F K e).hom ≫
        (Algebra.Homology.MapExtend.HomologicalComplex.mapExtendCanonicalIso G ((F.mapHomologicalComplex c).obj K) e).hom := by
  refine HomologicalComplex.hom_ext _ _ (fun j ↦ ?_)
  change (Algebra.Homology.MapExtend.HomologicalComplex.mapExtendCanonicalXIso (F ⋙ G) K (e.r j)).hom =
    G.map (Algebra.Homology.MapExtend.HomologicalComplex.mapExtendCanonicalXIso F K (e.r j)).hom ≫
      (Algebra.Homology.MapExtend.HomologicalComplex.mapExtendCanonicalXIso G ((F.mapHomologicalComplex c).obj K)
        (e.r j)).hom
  generalize e.r j = a
  cases a with
  | none => exact ((F ⋙ G).map_isZero (Limits.isZero_zero C)).eq_of_src _ _
  | some i => simp [Algebra.Homology.MapExtend.HomologicalComplex.mapExtendCanonicalXIso]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- A natural transformation followed by an actual complex map commutes with extension. -/
theorem mapExtendNaturalComposite (H : C ⥤ E) [H.Additive] (a : H ⟶ F ⋙ G)
    (K : HomologicalComplex C c) (L : HomologicalComplex D c)
    (p : (F.mapHomologicalComplex c).obj K ⟶ L) (e : c.Embedding c') :
    (a.mapHomologicalComplex c').app (K.extend e) ≫
        (G.mapHomologicalComplex c').map
          ((Algebra.Homology.MapExtend.HomologicalComplex.mapExtendCanonicalIso F K e).hom ≫
            HomologicalComplex.extendMap p e) ≫
        (Algebra.Homology.MapExtend.HomologicalComplex.mapExtendCanonicalIso G L e).hom =
      (Algebra.Homology.MapExtend.HomologicalComplex.mapExtendCanonicalIso H K e).hom ≫
        HomologicalComplex.extendMap
          ((a.mapHomologicalComplex c).app K ≫ (G.mapHomologicalComplex c).map p) e := by
  calc
    _ = (a.mapHomologicalComplex c').app (K.extend e) ≫
        (G.mapHomologicalComplex c').map
          (Algebra.Homology.MapExtend.HomologicalComplex.mapExtendCanonicalIso F K e).hom ≫
        ((G.mapHomologicalComplex c').map (HomologicalComplex.extendMap p e) ≫
          (Algebra.Homology.MapExtend.HomologicalComplex.mapExtendCanonicalIso G L e).hom) := by
      rw [Functor.map_comp]
      simp only [Category.assoc]
    _ = (a.mapHomologicalComplex c').app (K.extend e) ≫
        (G.mapHomologicalComplex c').map
          (Algebra.Homology.MapExtend.HomologicalComplex.mapExtendCanonicalIso F K e).hom ≫
        ((Algebra.Homology.MapExtend.HomologicalComplex.mapExtendCanonicalIso G ((F.mapHomologicalComplex c).obj K) e).hom ≫
          HomologicalComplex.extendMap ((G.mapHomologicalComplex c).map p) e) := by
      rw [Algebra.Homology.MapExtend.HomologicalComplex.mapExtendCanonicalIso_naturality]
    _ = ((a.mapHomologicalComplex c').app (K.extend e) ≫
          (Algebra.Homology.MapExtend.HomologicalComplex.mapExtendCanonicalIso (F ⋙ G) K e).hom) ≫
        HomologicalComplex.extendMap ((G.mapHomologicalComplex c).map p) e := by
      rw [mapExtendCanonicalIso_comp F G K e]
      simp only [Category.assoc]
    _ = ((Algebra.Homology.MapExtend.HomologicalComplex.mapExtendCanonicalIso H K e).hom ≫
          HomologicalComplex.extendMap ((a.mapHomologicalComplex c).app K) e) ≫
        HomologicalComplex.extendMap ((G.mapHomologicalComplex c).map p) e := by
      rw [Algebra.Homology.MapExtend.HomologicalComplex.mapExtendCanonicalIso_natTrans]
    _ = _ := by rw [Category.assoc, ← HomologicalComplex.extendMap_comp]

end

end OAI.AlgebraicGeometry.ComplexMultiplication.MapExtendComposition

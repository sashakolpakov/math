import OAI.AlgebraicGeometry.Picard.PoincareBundle.Line.SymmetryFibers

/-! # Symmetry Formula Fibers -/

namespace OAI.AlgebraicGeometry.Picard.PoincareBundle.Line.SymmetryFormulaFibers

noncomputable section

/-! A genuine equivariant line isomorphism intertwines the corresponding symmetries on every test fiber. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

theorem functor_intertwines {C D : Type*} [Category C] [Category D]
    (F H : C ⥤ D) (G : C ⥤ C) (c : H ≅ G ⋙ F)
    {M N : C} (e : M ≅ N) (a : G.obj M ≅ M) (b : G.obj N ≅ N)
    (he : G.mapIso e ≪≫ b = a ≪≫ e) :
    H.mapIso e ≪≫ (c.app N ≪≫ F.mapIso b) = (c.app M ≪≫ F.mapIso a) ≪≫ F.mapIso e := by
  apply Iso.ext
  have hn := c.hom.naturality e.hom
  dsimp only [Functor.comp_map] at hn
  have hh := congrArg (fun q => F.map q) (congrArg Iso.hom he)
  simp only [Iso.trans_hom, Functor.mapIso_hom, Functor.map_comp] at hh ⊢
  change H.map e.hom ≫ c.hom.app N ≫ F.map b.hom = (c.hom.app M ≫ F.map a.hom) ≫ F.map e.hom
  rw [← Category.assoc, hn, Category.assoc, hh, Category.assoc]

variable {S : Scheme.{u}} {E : Over S} (M N : Bundles.LineBundle E.left)
  (g : E ⟶ E) (e : M.sheaf ≅ N.sheaf)
  (a : (Scheme.Modules.pullback g.left).obj M.sheaf ≅ M.sheaf)
  (b : (Scheme.Modules.pullback g.left).obj N.sheaf ≅ N.sheaf)

/-- The original formula symmetry evaluates between the actual fibers at qg and q. -/
theorem atPoint (he : (Scheme.Modules.pullback g.left).mapIso e ≪≫ b = a ≪≫ e)
    {T : Over S} (q : T ⟶ E) :
    (Scheme.Modules.pullback (q ≫ g).left).mapIso e ≪≫ SymmetryFibers.atPoint N g b q =
      SymmetryFibers.atPoint M g a q ≪≫ (Scheme.Modules.pullback q.left).mapIso e := by
  rw [SymmetryFibers.atPoint_eq, SymmetryFibers.atPoint_eq]
  exact functor_intertwines (Scheme.Modules.pullback q.left) (Scheme.Modules.pullback (q ≫ g).left)
    (Scheme.Modules.pullback g.left) (Scheme.Modules.pullbackComp q.left g.left).symm e a b he

end

end OAI.AlgebraicGeometry.Picard.PoincareBundle.Line.SymmetryFormulaFibers

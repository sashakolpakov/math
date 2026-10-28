import OAI.AlgebraicGeometry.Picard.PoincareBundle.Line.SymmetryFibers

/-! # Restricted Line Equivariance -/

namespace OAI.AlgebraicGeometry.Picard.PoincareBundle.RestrictedLineEquivariance

noncomputable section

/-! Actual equivariant line isomorphisms remain equivariant on invariant scheme restrictions. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

open OAI.AlgebraicGeometry.Picard.PoincareBundle.Line.Fibers

theorem functor_intertwines {C D : Type*} [Category C] [Category D]
    (F : C ⥤ D) (G : C ⥤ C) (B : D ⥤ D) (c : F ⋙ B ≅ G ⋙ F)
    {M N : C} (e : M ≅ N) (a : G.obj M ≅ M) (b : G.obj N ≅ N)
    (he : G.mapIso e ≪≫ b = a ≪≫ e) :
    B.mapIso (F.mapIso e) ≪≫ (c.app N ≪≫ F.mapIso b) =
      (c.app M ≪≫ F.mapIso a) ≪≫ F.mapIso e := by
  apply Iso.ext
  have hn := c.hom.naturality e.hom
  dsimp only [Functor.comp_map] at hn
  have hh := congrArg (fun q => F.map q) (congrArg Iso.hom he)
  simp only [Iso.trans_hom, Functor.mapIso_hom, Functor.map_comp] at hh ⊢
  change B.map (F.map e.hom) ≫ c.hom.app N ≫ F.map b.hom =
    (c.hom.app M ≫ F.map a.hom) ≫ F.map e.hom
  rw [← Category.assoc, hn, Category.assoc, hh, Category.assoc]

variable {S : Scheme.{u}} {X Y : Over S} (p : X ⟶ Y) (g : Y ⟶ Y) (b : X ⟶ X)
  (h : b ≫ p = p ≫ g)

/-- The pullback comparison of the actual invariant square. -/
def comparison :
    Scheme.Modules.pullback p.left ⋙ Scheme.Modules.pullback b.left ≅
      Scheme.Modules.pullback g.left ⋙ Scheme.Modules.pullback p.left :=
  Scheme.Modules.pullbackComp b.left p.left ≪≫
    Scheme.Modules.pullbackCongr (congrArg Over.Hom.left h) ≪≫
      (Scheme.Modules.pullbackComp p.left g.left).symm

variable (L : Line.Bundles.LineBundle Y.left)
  (σ : (Scheme.Modules.pullback g.left).obj L.sheaf ≅ L.sheaf)

/-- Restrict a symmetry using the canonical geometric fiber comparisons. -/
def symmetry : (Scheme.Modules.pullback b.left).obj (Line.Fibers.fiber L p) ≅ Line.Fibers.fiber L p :=
  Line.Fibers.fiberPullbackIso L b p (p ≫ g) h ≪≫ Line.SymmetryFibers.atPoint L g σ p

theorem symmetry_eq : symmetry p g b h L σ =
    (comparison p g b h).app L.sheaf ≪≫ (Scheme.Modules.pullback p.left).mapIso σ := by
  rw [symmetry, Line.SymmetryFibers.atPoint_eq]
  rfl

/-- A genuine equivariant line formula restricts through every invariant square. -/
theorem equivariant (N : Line.Bundles.LineBundle Y.left) (e : L.sheaf ≅ N.sheaf)
    (τ : (Scheme.Modules.pullback g.left).obj N.sheaf ≅ N.sheaf)
    (he : (Scheme.Modules.pullback g.left).mapIso e ≪≫ τ = σ ≪≫ e) :
    (Scheme.Modules.pullback b.left).mapIso ((Scheme.Modules.pullback p.left).mapIso e) ≪≫
        symmetry p g b h N τ =
      symmetry p g b h L σ ≪≫ (Scheme.Modules.pullback p.left).mapIso e := by
  rw [symmetry_eq, symmetry_eq]
  exact functor_intertwines (Scheme.Modules.pullback p.left) (Scheme.Modules.pullback g.left)
    (Scheme.Modules.pullback b.left) (comparison p g b h) e σ τ he

end

end OAI.AlgebraicGeometry.Picard.PoincareBundle.RestrictedLineEquivariance

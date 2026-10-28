import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.LineHomRigidity

/-! # Rigidified Formula Equivariance -/

namespace OAI.AlgebraicGeometry.Picard.PoincareBundle.RigidifiedFormulaEquivariance

noncomputable section

/-! A line formula intertwines symmetries that agree with the canonical comparison on a detecting restriction. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

theorem map_intertwines {C D : Type*} [Category C] [Category D]
    (F : C ⥤ D) (G : C ⥤ C) (c : G ⋙ F ≅ F) {M N : C} (e : M ≅ N)
    (a : G.obj M ≅ M) (b : G.obj N ≅ N)
    (ha : F.mapIso a = c.app M) (hb : F.mapIso b = c.app N) :
    F.mapIso (G.mapIso e ≪≫ b) = F.mapIso (a ≪≫ e) := by
  apply Iso.ext
  simp only [Functor.mapIso_trans, Iso.trans_hom, Functor.mapIso_hom]
  have ha' := congrArg Iso.hom ha
  have hb' := congrArg Iso.hom hb
  change F.map (G.map e.hom) ≫ (F.mapIso b).hom = (F.mapIso a).hom ≫ F.map e.hom
  rw [ha', hb']
  exact c.hom.naturality e.hom

/-- Pullback to a locus preserving global functions detects equivariance of actual line isomorphisms. -/
theorem equivariance {X Y : Scheme.{u}} (p : X ⟶ Y) [IsIso p.appTop]
    (g : Y ⟶ Y) (h : p ≫ g = p) (L M : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle Y) (e : L.sheaf ≅ M.sheaf)
    (a : (L.pullback g).sheaf ≅ L.sheaf) (b : (M.pullback g).sheaf ≅ M.sheaf)
    (ha : (Scheme.Modules.pullback p).mapIso a =
      (Scheme.Modules.pullbackComp p g ≪≫ Scheme.Modules.pullbackCongr h).app L.sheaf)
    (hb : (Scheme.Modules.pullback p).mapIso b =
      (Scheme.Modules.pullbackComp p g ≪≫ Scheme.Modules.pullbackCongr h).app M.sheaf) :
    (Scheme.Modules.pullback g).mapIso e ≪≫ b = a ≪≫ e := by
  apply Quotients.FiniteDescent.LineRigidificationAt.Construction.LineRigidification.iso_unique p (L.pullback g) M
  exact map_intertwines (Scheme.Modules.pullback p) (Scheme.Modules.pullback g)
    (Scheme.Modules.pullbackComp p g ≪≫ Scheme.Modules.pullbackCongr h) e a b ha hb

end

end OAI.AlgebraicGeometry.Picard.PoincareBundle.RigidifiedFormulaEquivariance

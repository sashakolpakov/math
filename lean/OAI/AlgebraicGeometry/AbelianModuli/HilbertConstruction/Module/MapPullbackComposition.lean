import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Pullback.AssociativityFusion
import Mathlib.CategoryTheory.HomCongr

/-! # Map Pullback Composition -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Module.MapPullbackComposition

noncomputable section

/-! Composition of pullback for arbitrary maps upstairs, with associativity coherence. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

variable {W X Y Z : Scheme.{u}}

theorem moduleMap_homCongr_combine {A B C D E F : X.Modules}
    (eA : A ≅ C) (eB : B ≅ D) (fA : C ≅ E) (fB : D ≅ F) (φ : A ⟶ B) :
    Iso.homCongr fA fB (Iso.homCongr eA eB φ) = Iso.homCongr (eA ≪≫ fA) (eB ≪≫ fB) φ :=
  (Iso.homCongr_trans eA eB fA fB φ).symm

theorem moduleMap_homCongr_naturality (F G : X.Modules ⥤ Y.Modules) (e : F ≅ G)
    {M N : X.Modules} (φ : M ⟶ N) :
    Iso.homCongr (e.app M) (e.app N) (F.map φ) = G.map φ := by
  exact (congrArg (fun k => e.inv.app M ≫ k) (e.hom.naturality φ)).trans
    (e.inv_hom_id_app_assoc M _)

def moduleMapPullbackComp (a : X ⟶ Y) (f : Y ⟶ Z) {M N : Z.Modules}
    (φ : (Scheme.Modules.pullback f).obj M ⟶ (Scheme.Modules.pullback f).obj N) :
    (Scheme.Modules.pullback (a ≫ f)).obj M ⟶ (Scheme.Modules.pullback (a ≫ f)).obj N :=
  Iso.homCongr ((Scheme.Modules.pullbackComp a f).app M) ((Scheme.Modules.pullbackComp a f).app N)
    ((Scheme.Modules.pullback a).map φ)

theorem moduleMapPullbackComp_of_map (a : X ⟶ Y) (f : Y ⟶ Z) {M N : Z.Modules}
    (φ : M ⟶ N) : moduleMapPullbackComp a f ((Scheme.Modules.pullback f).map φ) =
      (Scheme.Modules.pullback (a ≫ f)).map φ :=
  moduleMap_homCongr_naturality _ _ (Scheme.Modules.pullbackComp a f) φ

theorem moduleMapPullbackComp_assoc (a : W ⟶ X) (b : X ⟶ Y) (f : Y ⟶ Z) {M N : Z.Modules}
    (φ : (Scheme.Modules.pullback f).obj M ⟶ (Scheme.Modules.pullback f).obj N) :
    Iso.homCongr ((Scheme.Modules.pullbackCongr (Category.assoc a b f).symm).app M)
      ((Scheme.Modules.pullbackCongr (Category.assoc a b f).symm).app N)
      (moduleMapPullbackComp a (b ≫ f) (moduleMapPullbackComp b f φ)) =
        moduleMapPullbackComp (a ≫ b) f φ := by
  unfold moduleMapPullbackComp
  rw [Functor.map_homCongr]
  rw [moduleMap_homCongr_combine, moduleMap_homCongr_combine,
    Pullback.AssociativityFusion.modulePullback_associativity_fusion, Pullback.AssociativityFusion.modulePullback_associativity_fusion, Iso.homCongr_trans]
  exact congrArg (fun k => Iso.homCongr ((Scheme.Modules.pullbackComp (a ≫ b) f).app M)
      ((Scheme.Modules.pullbackComp (a ≫ b) f).app N) k)
    (moduleMap_homCongr_naturality _ _ (Scheme.Modules.pullbackComp a b) φ)

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Module.MapPullbackComposition

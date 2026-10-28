import OAI.AlgebraicGeometry.Picard.PoincareBundle.Tensor.LinePullback
import OAI.AlgebraicGeometry.Picard.PoincareBundle.Tensor.UnitPullback

/-! # Comparison Paths -/

namespace OAI.AlgebraicGeometry.Picard.PoincareBundle.Tensor.ComparisonPaths

noncomputable section

/-!
# Canonical tensor pullback isomorphisms along composition and equality paths
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

open OAI.AlgebraicGeometry.Picard.PoincareBundle.Tensor.UnitPullback OAI.AlgebraicGeometry.Picard.PoincareBundle.Tensor.SheafMaps

variable {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
  (M N : Z.Modules) (hM : Line.Bundles.IsLine M) (hN : Line.Bundles.IsLine N)

/-- Composition coherence holds for the whole genuine tensor pullback isomorphism. -/
theorem composition_iso :
    LinePullback.pullbackIso (f ≫ g) M N hM hN ≪≫
      UnitPullback.tensorIso ((Scheme.Modules.pullbackComp f g).symm.app M) ((Scheme.Modules.pullbackComp f g).symm.app N) =
    (Scheme.Modules.pullbackComp f g).symm.app (AbelianModuli.HilbertConstruction.Tensor.ProductSheaf.tensorModule M N) ≪≫
      (Scheme.Modules.pullback f).mapIso (LinePullback.pullbackIso g M N hM hN) ≪≫
      LinePullback.pullbackIso f ((Scheme.Modules.pullback g).obj M) ((Scheme.Modules.pullback g).obj N)
        (hM.pullback g) (hN.pullback g) := by
  apply Iso.ext
  exact PullbackComposition.pullbackMap_comp_inv f g M N

variable {f} {f' : X ⟶ Y}

/-- Equality of scheme morphisms intertwines their canonical tensor pullback isomorphisms. -/
theorem congr_iso (h : f = f') (P Q : Y.Modules)
    (hP : Line.Bundles.IsLine P) (hQ : Line.Bundles.IsLine Q) :
    (Scheme.Modules.pullbackCongr h).app (AbelianModuli.HilbertConstruction.Tensor.ProductSheaf.tensorModule P Q) ≪≫ LinePullback.pullbackIso f' P Q hP hQ =
      LinePullback.pullbackIso f P Q hP hQ ≪≫
        UnitPullback.tensorIso ((Scheme.Modules.pullbackCongr h).app P) ((Scheme.Modules.pullbackCongr h).app Q) := by
  subst f'
  apply Iso.ext
  simp only [Scheme.Modules.pullbackCongr, eqToIso_refl, Iso.trans_hom]
  change (𝟙 _) ≫ _ = _ ≫ SheafMaps.tensorMap (𝟙 _) (𝟙 _)
  rw [Category.id_comp, SheafMaps.tensorMap_id, Category.comp_id]

end

end OAI.AlgebraicGeometry.Picard.PoincareBundle.Tensor.ComparisonPaths

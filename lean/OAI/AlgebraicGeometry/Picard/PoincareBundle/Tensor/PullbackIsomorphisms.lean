import OAI.AlgebraicGeometry.Picard.PoincareBundle.Tensor.PullbackComposition
import OAI.AlgebraicGeometry.Picard.PoincareBundle.Tensor.UnitPullback

/-! # Pullback Isomorphisms -/

namespace OAI.AlgebraicGeometry.Picard.PoincareBundle.Tensor.PullbackIsomorphisms

noncomputable section

/-!
# Detecting invertibility of the canonical tensor pullback comparison
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

open OAI.AlgebraicGeometry.Picard.PoincareBundle.Tensor.SheafMaps OAI.AlgebraicGeometry.Picard.PoincareBundle.Tensor.PullbackMap OAI.AlgebraicGeometry.Picard.PoincareBundle.Tensor.UnitPullback

variable {X Y : Scheme.{u}} (f : X ⟶ Y)

/-- Replacing either original sheaf by an isomorphic sheaf preserves invertibility of the comparison. -/
theorem input_isIso_iff {M M' N N' : Y.Modules} (a : M ≅ M') (b : N ≅ N') :
    IsIso (PullbackMap.pullbackMap f M N) ↔ IsIso (PullbackMap.pullbackMap f M' N') := by
  calc
    IsIso (PullbackMap.pullbackMap f M N) ↔ IsIso (PullbackMap.pullbackMap f M N ≫
        SheafMaps.tensorMap ((Scheme.Modules.pullback f).map a.hom) ((Scheme.Modules.pullback f).map b.hom)) :=
      (isIso_comp_right_iff _ _).symm
    _ ↔ IsIso ((Scheme.Modules.pullback f).map (SheafMaps.tensorMap a.hom b.hom) ≫ PullbackMap.pullbackMap f M' N') := by
      rw [PullbackMap.pullbackMap_naturality]
    _ ↔ IsIso (PullbackMap.pullbackMap f M' N') := isIso_comp_left_iff _ _

variable {Z : Scheme.{u}} (g : Y ⟶ Z) (M N : Z.Modules)

/-- Invertibility of the composite comparison is equivalent to invertibility of the successive maps. -/
theorem comp_isIso_iff :
    IsIso (PullbackMap.pullbackMap (f ≫ g) M N) ↔
      IsIso ((Scheme.Modules.pullback f).map (PullbackMap.pullbackMap g M N) ≫
        PullbackMap.pullbackMap f ((Scheme.Modules.pullback g).obj M) ((Scheme.Modules.pullback g).obj N)) := by
  calc
    IsIso (PullbackMap.pullbackMap (f ≫ g) M N) ↔ IsIso (PullbackMap.pullbackMap (f ≫ g) M N ≫
        SheafMaps.tensorMap ((Scheme.Modules.pullbackComp f g).inv.app M) ((Scheme.Modules.pullbackComp f g).inv.app N)) :=
      (isIso_comp_right_iff _ _).symm
    _ ↔ IsIso ((Scheme.Modules.pullbackComp f g).inv.app (AbelianModuli.HilbertConstruction.Tensor.ProductSheaf.tensorModule M N) ≫
        (Scheme.Modules.pullback f).map (PullbackMap.pullbackMap g M N) ≫
          PullbackMap.pullbackMap f ((Scheme.Modules.pullback g).obj M) ((Scheme.Modules.pullback g).obj N)) := by
      rw [PullbackComposition.pullbackMap_comp_inv]
    _ ↔ _ := isIso_comp_left_iff _ _

/-- When the last comparison is invertible, the composite detects the pullback of the first comparison. -/
theorem comp_map_isIso_iff
    (hf : IsIso (PullbackMap.pullbackMap f ((Scheme.Modules.pullback g).obj M) ((Scheme.Modules.pullback g).obj N))) :
    IsIso (PullbackMap.pullbackMap (f ≫ g) M N) ↔ IsIso ((Scheme.Modules.pullback f).map (PullbackMap.pullbackMap g M N)) :=
  (comp_isIso_iff f g M N).trans (@isIso_comp_right_iff _ _ _ _ _ _ _ hf)

/-- Successive invertible canonical tensor comparisons give an invertible composite comparison. -/
theorem comp_isIso
    (hf : IsIso (PullbackMap.pullbackMap f ((Scheme.Modules.pullback g).obj M) ((Scheme.Modules.pullback g).obj N)))
    (hg : IsIso (PullbackMap.pullbackMap g M N)) : IsIso (PullbackMap.pullbackMap (f ≫ g) M N) := by
  apply (comp_map_isIso_iff f g M N hf).mpr
  exact @Functor.map_isIso _ _ _ _ _ _ (Scheme.Modules.pullback f) (PullbackMap.pullbackMap g M N) hg

end

end OAI.AlgebraicGeometry.Picard.PoincareBundle.Tensor.PullbackIsomorphisms

import OAI.AlgebraicGeometry.Picard.PoincareBundle.Tensor.LineBundles
import OAI.AlgebraicGeometry.Picard.PoincareBundle.Bilinear.BilinearPullback
import OAI.AlgebraicGeometry.Picard.PoincareBundle.Ordinary.GlobalLineDescent
import OAI.AlgebraicGeometry.Picard.PoincareBundle.Cech.InvariantUniversal
import OAI.AlgebraicGeometry.Picard.PoincareBundle.FaithfulPullback

/-! # Global Descent -/

namespace OAI.AlgebraicGeometry.Picard.PoincareBundle.Bilinear.GlobalDescent

noncomputable section

/-!
# Effective descent of equivariant bilinear structure maps on actual line bundles
-/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

universe u

open OAI.AlgebraicGeometry.Picard.PoincareBundle.Tensor.SheafMaps OAI.AlgebraicGeometry.Picard.PoincareBundle.Bilinear.BilinearPullback
open OAI.AlgebraicGeometry.Picard.PoincareBundle.Geometric.KernelLinearization OAI.AlgebraicGeometry.Picard.PoincareBundle.Geometric.CechInvariant OAI.AlgebraicGeometry.Picard.PoincareBundle.Ordinary.GlobalLineDescent

variable {X Y : Scheme.{u}} (f : X ⟶ Y)
  (D : Geometric.KernelLinearization.modulePullbacks.DescentData (fun (_ : PUnit.{1}) => f))
  (hD : Line.Bundles.IsLine (D.obj PUnit.unit))
  (M N : Line.Bundles.LineBundle Y) {A B : X.Modules}
  (eM : (Scheme.Modules.pullback f).obj M.sheaf ≅ A)
  (eN : (Scheme.Modules.pullback f).obj N.sheaf ≅ B)
  (β : AbelianModuli.HilbertConstruction.Bilinear.Sheaves.SheafBilinearMap A B (D.obj PUnit.unit))

/-- The actual cover morphism represented by the bilinear operation and the two input recoveries. -/
def coverMap : (Scheme.Modules.pullback f).obj (AbelianModuli.HilbertConstruction.Tensor.ProductSheaf.tensorModule M.sheaf N.sheaf) ⟶ D.obj PUnit.unit :=
  (Tensor.LinePullback.pullbackIso f M.sheaf N.sheaf M.isLine N.isLine).hom ≫
    Tensor.SheafMaps.tensorMap eM.hom eN.hom ≫ BilinearPullback.toHom β

/-- Equivariance is the ordinary geometric gluing square for the represented bilinear operation. -/
def Compatible : Prop :=
  (Scheme.Modules.pullback (pullback.fst f f)).map (coverMap f D M N eM eN β) ≫ (Geometric.CechInvariant.relationGluing f D).hom =
    (Cech.MateNormalization.standardGluing f (pullback.fst f f) (pullback.snd f f)
      pullback.condition).hom.app (AbelianModuli.HilbertConstruction.Tensor.ProductSheaf.tensorModule M.sheaf N.sheaf) ≫
      (Scheme.Modules.pullback (pullback.snd f f)).map (coverMap f D M N eM eN β)

variable [IsAffineHom f] [IsLocallyNoetherian Y] [Flat f] [Surjective f]
  (hβ : Compatible f D M N eM eN β)

include hβ in
/-- The equivariant bilinear operation has one and only one represented morphism on the quotient. -/
theorem existsUnique_map :
    ∃! a : AbelianModuli.HilbertConstruction.Tensor.ProductSheaf.tensorModule M.sheaf N.sheaf ⟶ (Ordinary.GlobalLineDescent.descendedLine f D hD).sheaf,
      (Scheme.Modules.pullback f).map a ≫ Geometric.CechInvariant.ordinaryComparison f D = coverMap f D M N eM eN β :=
  Cech.InvariantUniversal.existsUnique_lift f (pullback.fst f f) (pullback.snd f f) pullback.condition
    (D.obj PUnit.unit) (Geometric.CechInvariant.relationGluing f D) (AbelianModuli.HilbertConstruction.Tensor.ProductSheaf.tensorModule M.sheaf N.sheaf)
    ⟨coverMap f D M N eM eN β, hβ⟩

/-- The unique actual sheaf morphism descended from the equivariant bilinear operation. -/
def descendedHom : AbelianModuli.HilbertConstruction.Tensor.ProductSheaf.tensorModule M.sheaf N.sheaf ⟶ (Ordinary.GlobalLineDescent.descendedLine f D hD).sheaf :=
  (existsUnique_map f D hD M N eM eN β hβ).choose

theorem descendedHom_fac :
    (Scheme.Modules.pullback f).map (descendedHom f D hD M N eM eN β hβ) ≫ Geometric.CechInvariant.ordinaryComparison f D =
      coverMap f D M N eM eN β :=
  (existsUnique_map f D hD M N eM eN β hβ).choose_spec.1

/-- The descended operation is an actual sectionwise bilinear map of the quotient line bundles. -/
def descendedBilinear : AbelianModuli.HilbertConstruction.Bilinear.Sheaves.SheafBilinearMap M.sheaf N.sheaf (Ordinary.GlobalLineDescent.descendedLine f D hD).sheaf :=
  AbelianModuli.HilbertConstruction.Bilinear.Sheaves.SheafBilinearMap.tensorHomEquiv _ _ _ (descendedHom f D hD M N eM eN β hβ)

/-- Its represented morphism is exactly the uniquely descended sheaf morphism. -/
theorem toHom_descendedBilinear :
    BilinearPullback.toHom (descendedBilinear f D hD M N eM eN β hβ) = descendedHom f D hD M N eM eN β hβ :=
  (AbelianModuli.HilbertConstruction.Bilinear.Sheaves.SheafBilinearMap.tensorHomEquiv _ _ _).symm_apply_apply _

include hβ in
/-- The descended bilinear map is unique with its exact pullback factorization. -/
theorem existsUnique_bilinear :
    ∃! δ : AbelianModuli.HilbertConstruction.Bilinear.Sheaves.SheafBilinearMap M.sheaf N.sheaf (Ordinary.GlobalLineDescent.descendedLine f D hD).sheaf,
      (Scheme.Modules.pullback f).map (BilinearPullback.toHom δ) ≫ Geometric.CechInvariant.ordinaryComparison f D = coverMap f D M N eM eN β := by
  refine ⟨descendedBilinear f D hD M N eM eN β hβ, ?_, ?_⟩
  · change (Scheme.Modules.pullback f).map (BilinearPullback.toHom (descendedBilinear f D hD M N eM eN β hβ)) ≫
      Geometric.CechInvariant.ordinaryComparison f D = _
    rw [toHom_descendedBilinear]
    exact descendedHom_fac f D hD M N eM eN β hβ
  · intro δ hδ
    apply (AbelianModuli.HilbertConstruction.Bilinear.Sheaves.SheafBilinearMap.tensorHomEquiv _ _ _).symm.injective
    change BilinearPullback.toHom δ = BilinearPullback.toHom _
    rw [toHom_descendedBilinear]
    exact (existsUnique_map f D hD M N eM eN β hβ).choose_spec.2 (BilinearPullback.toHom δ) hδ

/-- A bilinear line-bundle isomorphism descends to a bilinear line-bundle isomorphism. -/
theorem descendedHom_isIso (hi : IsIso (BilinearPullback.toHom β)) : IsIso (descendedHom f D hD M N eM eN β hβ) := by
  have hc : IsIso (coverMap f D M N eM eN β) := by
    exact (Tensor.LinePullback.pullbackIso f M.sheaf N.sheaf M.isLine N.isLine ≪≫
      Tensor.UnitPullback.tensorIso eM eN ≪≫ @asIso _ _ _ _ (BilinearPullback.toHom β) hi).isIso_hom
  have hd : IsIso (Geometric.CechInvariant.ordinaryComparison f D) := Ordinary.GlobalLineDescent.comparison_isIso f D hD
  have hm : IsIso ((Scheme.Modules.pullback f).map (descendedHom f D hD M N eM eN β hβ) ≫
      Geometric.CechInvariant.ordinaryComparison f D) := by
    rw [descendedHom_fac]
    exact hc
  have hp : IsIso ((Scheme.Modules.pullback f).map (descendedHom f D hD M N eM eN β hβ)) :=
    (@isIso_comp_right_iff _ _ _ _ _ _ _ hd).mp hm
  exact FaithfulPullback.isIso_of_pullback f _ (Tensor.LineBundles.tensor_isLine M.isLine N.isLine)
    (Ordinary.GlobalLineDescent.invariant_isLine f D hD) hp

end

end OAI.AlgebraicGeometry.Picard.PoincareBundle.Bilinear.GlobalDescent

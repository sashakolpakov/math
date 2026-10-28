import OAI.AlgebraicGeometry.PELModuli.IntegralModel.NormalizedPicardLocal
import OAI.AlgebraicGeometry.PELModuli.IntegralModel.Picard.LineHomDescent
import OAI.AlgebraicGeometry.Isogenies.NeighborCounting.ProductTestFactors
import OAI.AlgebraicGeometry.Isogenies.NeighborCounting.PullHomCommonFactor
import OAI.AlgebraicGeometry.PELModuli.IntegralModel.IsogenyFactorizationIs

/-! # Normalized Picard Descent -/

namespace OAI.AlgebraicGeometry.PELModuli.IntegralModel.NormalizedPicardDescent.NormalizedPicard

noncomputable section

/-! Normalized local line-bundle comparisons on an abelian product
family satisfy descent automatically. Their overlap equations are proved
using universal constancy of functions and the actual zero sections. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj

open OAI.AlgebraicGeometry.Isogenies.NeighborCounting.PoincareNormalization OAI.AlgebraicGeometry.Isogenies.NeighborCounting.FramedPullback
open OAI.AlgebraicGeometry.Isogenies.NeighborCounting.ProductTestFactors

variable {k : Type} [Field k] [IsAlgClosed k] {g : ℕ}
  (A : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g (Spec (.of k)))
  {T U : Over (Spec (.of k))} (u : U ⟶ T)
  (L M : (T ⊗ A.scheme).left.Modules)
  (eL : (Scheme.Modules.pullback (Isogenies.NeighborCounting.PoincareNormalization.familyZero A T).left).obj L ≅ ArithmeticGeometry.OrdinaryLocus.Openness.LineBundle.Construction.structureSheafModule T.left)
  (eM : (Scheme.Modules.pullback (Isogenies.NeighborCounting.PoincareNormalization.familyZero A T).left).obj M ≅ ArithmeticGeometry.OrdinaryLocus.Openness.LineBundle.Construction.structureSheafModule T.left)
  (e : (Scheme.Modules.pullback (u ▷ A.scheme).left).obj L ≅
    (Scheme.Modules.pullback (u ▷ A.scheme).left).obj M)

theorem restrictions_eq (hL : ArithmeticGeometry.OrdinaryLocus.Openness.LineBundle.Construction.IsLineBundle L) {V : Over (Spec (.of k))} (a b : V ⟶ U) (p : V ⟶ T)
    (ha : a ≫ u = p) (hb : b ≫ u = p) :
    NormalizedPicardLocal.NormalizedPicard.restrict A u L M eL eM a p ha e = NormalizedPicardLocal.NormalizedPicard.restrict A u L M eL eM b p hb e := by
  have : ConnectedSpace A.scheme.left := GeometricallyConnected.connectedSpace_of_subsingleton A.scheme.hom
  have : IsIntegral A.scheme.left := ArithmeticGeometry.Models.SpreadingOut.SmoothGeometricIntegrality.Construction.smooth_connected_scheme_integral A.scheme.hom
  have hΓ : IsIso (fst V A.scheme).left.appTop := Picard.GlobalFunctions.PicardFunctions.isIso_properBaseChange_app V A.scheme ⊤
  exact Picard.NormalizedZeroComparison.PicardNormalizedZeroComparison.iso_eq_of_intrinsic_normalization
    (p ▷ A.scheme).left (Isogenies.NeighborCounting.PoincareNormalization.familyZero A T).left (Isogenies.NeighborCounting.PoincareNormalization.familyZero A V).left p.left
    (congrArg Over.Hom.left (Isogenies.NeighborCounting.PoincareNormalization.familyZero_naturality A p))
    (fst V A.scheme).left (Isogenies.NeighborCounting.PoincareNormalization.familyZero_projection A V)
    (ConcreteCategory.bijective_of_isIso (fst V A.scheme).left.appTop).surjective
    (ArithmeticGeometry.OrdinaryLocus.Openness.LineBundle.Construction.isLineBundle_pullback (p ▷ A.scheme).left L hL)
    _ _ (eL.hom ≫ eM.inv)
    (NormalizedPicardLocal.NormalizedPicard.restrict_intrinsic A u L M eL eM a p ha e)
    (NormalizedPicardLocal.NormalizedPicard.restrict_intrinsic A u L M eL eM b p hb e)

/-- The normalized comparison agrees under all pairs of scheme maps
with the same image, including maps from nonreduced test schemes. -/
theorem normalize_compatible (hL : ArithmeticGeometry.OrdinaryLocus.Openness.LineBundle.Construction.IsLineBundle L) :
    Isogenies.NeighborCounting.FramedDescent.CompatibleHom (u ▷ A.scheme).left (NormalizedPicardLocal.NormalizedPicard.normalize A u L M eL eM e).hom := by
  intro Z x y p hx hy
  let a := Isogenies.NeighborCounting.ProductTestFactors.baseMap A.scheme u p x hx
  let b := Isogenies.NeighborCounting.ProductTestFactors.baseMap A.scheme u p y hy
  let pB := Isogenies.NeighborCounting.ProductTestFactors.baseTarget A.scheme p
  have ha : a ≫ u = pB := Isogenies.NeighborCounting.ProductTestFactors.baseMap_comp A.scheme u p x hx
  have hb : b ≫ u = pB := Isogenies.NeighborCounting.ProductTestFactors.baseMap_comp A.scheme u p y hy
  have heq : Isogenies.NeighborCounting.FramedPullback.pullbackHomTo (a ▷ A.scheme).left (u ▷ A.scheme).left (pB ▷ A.scheme).left
        (NormalizedPicardLocal.NormalizedPicard.product_comp A u a pB ha) (NormalizedPicardLocal.NormalizedPicard.normalize A u L M eL eM e).hom =
      Isogenies.NeighborCounting.FramedPullback.pullbackHomTo (b ▷ A.scheme).left (u ▷ A.scheme).left (pB ▷ A.scheme).left
        (NormalizedPicardLocal.NormalizedPicard.product_comp A u b pB hb) (NormalizedPicardLocal.NormalizedPicard.normalize A u L M eL eM e).hom := by
    simpa only [NormalizedPicardLocal.NormalizedPicard.restrict, Isogenies.NeighborCounting.FramedPullback.pullbackIsoTo_hom] using
      congrArg Iso.hom (restrictions_eq A u L M eL eM e hL a b pB ha hb)
  exact Isogenies.NeighborCounting.PullHomCommonFactor.native_common_factor (u ▷ A.scheme).left
    (NormalizedPicardLocal.NormalizedPicard.normalize A u L M eL eM e).hom
    (a ▷ A.scheme).left (b ▷ A.scheme).left (pB ▷ A.scheme).left
    (NormalizedPicardLocal.NormalizedPicard.product_comp A u a pB ha) (NormalizedPicardLocal.NormalizedPicard.product_comp A u b pB hb) heq
    (Isogenies.NeighborCounting.ProductTestFactors.graph A.scheme p).left x y p
    (Isogenies.NeighborCounting.ProductTestFactors.graph_to_test A.scheme u p x hx) (Isogenies.NeighborCounting.ProductTestFactors.graph_to_test A.scheme u p y hy)
    (Isogenies.NeighborCounting.ProductTestFactors.graph_to_target A.scheme p) hx hy

/-- An actual local line-bundle isomorphism over an fpqc parameter cover
descends after canonical normalization at the zero section. -/
theorem normalize_descends (hL : ArithmeticGeometry.OrdinaryLocus.Openness.LineBundle.Construction.IsLineBundle L) (hM : ArithmeticGeometry.OrdinaryLocus.Openness.LineBundle.Construction.IsLineBundle M) [Flat u.left] [Surjective u.left] [QuasiCompact u.left] :
    ∃! d : L ≅ M,
      (Scheme.Modules.pullback (u ▷ A.scheme).left).mapIso d = NormalizedPicardLocal.NormalizedPicard.normalize A u L M eL eM e := by
  let : MorphismProperty.IsStableUnderComposition (@AlgebraicGeometry.Surjective) :=
    ⟨fun _ _ hf hg => ⟨hg.1.comp hf.1⟩⟩
  have : Flat (u ▷ A.scheme).left := by
    simpa only [tensorHom_id] using IsogenyFactorizationIs.IsogenyFactorization.property_tensor_over (@Flat)
      u (𝟙 A.scheme) inferInstance (inferInstanceAs (Flat (𝟙 A.scheme.left)))
  have : Surjective (u ▷ A.scheme).left := by
    simpa only [tensorHom_id] using IsogenyFactorizationIs.IsogenyFactorization.property_tensor_over (@AlgebraicGeometry.Surjective)
      u (𝟙 A.scheme) inferInstance (inferInstanceAs (Surjective (𝟙 A.scheme.left)))
  have : QuasiCompact (u ▷ A.scheme).left := by
    simpa only [tensorHom_id] using IsogenyFactorizationIs.IsogenyFactorization.property_tensor_over (@QuasiCompact)
      u (𝟙 A.scheme) inferInstance (inferInstanceAs (QuasiCompact (𝟙 A.scheme.left)))
  exact Picard.LineHomDescent.PicardLineHomDescent.existsUnique_lineIso_descent (u ▷ A.scheme).left
    hL hM (NormalizedPicardLocal.NormalizedPicard.normalize A u L M eL eM e)
    (normalize_compatible A u L M eL eM e hL)

end

end OAI.AlgebraicGeometry.PELModuli.IntegralModel.NormalizedPicardDescent.NormalizedPicard

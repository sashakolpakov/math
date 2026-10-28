import OAI.AlgebraicGeometry.Picard.PoincareBundle.RelativeComparison
import OAI.AlgebraicGeometry.PELModuli.IntegralModel.NormalizedPicardInjection

/-! # Normalized Comparison -/

namespace OAI.AlgebraicGeometry.Picard.PoincareBundle.NormalizedComparison

noncomputable section

/-! Equality in PoincareBundle's relative Picard sheaf gives an actual normalized line isomorphism. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry Opposite
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj

open OAI.AlgebraicGeometry.Picard.PoincareBundle.Line.Comparison.Bundle

variable {k : Type} [Field k] [IsAlgClosed k] {g : ℕ}
  (A : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g (Spec (.of k)))
  {T : Over (Spec (.of k))} [CompactSpace T.left] [QuasiSeparatedSpace T.left]
  (L M : Line.Bundles.LineBundle (T ⊗ A.scheme).left)
  (eL : (Scheme.Modules.pullback (lift (𝟙 T) (1 : T ⟶ A.scheme)).left).obj L.sheaf ≅ AbelianModuli.HilbertConstruction.Line.Bundles.structureModule T.left)
  (eM : (Scheme.Modules.pullback (lift (𝟙 T) (1 : T ⟶ A.scheme)).left).obj M.sheaf ≅ AbelianModuli.HilbertConstruction.Line.Bundles.structureModule T.left)

include eL eM

/-- The actual comparison descends from Picard equality and preserves the prescribed zero frames. -/
theorem normalized_iso_of_picard_eq
    (h : (Functor.toRelativePicard A.scheme).app (op T) (Line.Bundles.LineBundleClass.mk L) =
      (Functor.toRelativePicard A.scheme).app (op T) (Line.Bundles.LineBundleClass.mk M)) :
    ∃ d : L.sheaf ≅ M.sheaf,
      (Scheme.Modules.pullback (lift (𝟙 T) (1 : T ⟶ A.scheme)).left).map d.hom ≫ eM.hom = eL.hom := by
  have hs := congrArg ((RelativeComparison.sheafIso A.scheme).hom.hom.app (op T)) h
  have hs' := (RelativeComparison.section_comparison A.scheme
    (Line.Bundles.LineBundleClass.mk L)).symm.trans
    (hs.trans (RelativeComparison.section_comparison A.scheme (Line.Bundles.LineBundleClass.mk M)))
  exact PELModuli.IntegralModel.NormalizedPicardInjection.NormalizedPicard.normalized_iso_of_picard_eq A (Line.Comparison.Bundle.toShared L) (Line.Comparison.Bundle.toShared M) eL eM hs'

omit [CompactSpace T.left] [QuasiSeparatedSpace T.left] in
/-- Proper connected geometry makes the normalized family comparison unique, even for nonreduced parameters. -/
theorem normalized_iso_unique (d e : L.sheaf ≅ M.sheaf)
    (hd : (Scheme.Modules.pullback (lift (𝟙 T) (1 : T ⟶ A.scheme)).left).map d.hom ≫ eM.hom = eL.hom)
    (he : (Scheme.Modules.pullback (lift (𝟙 T) (1 : T ⟶ A.scheme)).left).map e.hom ≫ eM.hom = eL.hom) : d = e := by
  have : ConnectedSpace A.scheme.left := GeometricallyConnected.connectedSpace_of_subsingleton A.scheme.hom
  have : IsIntegral A.scheme.left := ArithmeticGeometry.Models.SpreadingOut.SmoothGeometricIntegrality.Construction.smooth_connected_scheme_integral A.scheme.hom
  exact PELModuli.IntegralModel.Picard.RigidifiedUniqueness.PicardRigidifiedUniqueness.proper_product_normalizedIso_unique T A.scheme
    (lift (𝟙 T) (1 : T ⟶ A.scheme)).left
    (congrArg Over.Hom.left (lift_fst (𝟙 T) (1 : T ⟶ A.scheme))) L.isLine eL eM d e hd he

end

end OAI.AlgebraicGeometry.Picard.PoincareBundle.NormalizedComparison

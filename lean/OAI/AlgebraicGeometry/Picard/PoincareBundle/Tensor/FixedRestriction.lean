import OAI.AlgebraicGeometry.Picard.PoincareBundle.Tensor.LineIsoCoherence
import OAI.AlgebraicGeometry.Picard.PoincareBundle.Tensor.CongrComposition

/-! # Fixed Restriction -/

namespace OAI.AlgebraicGeometry.Picard.PoincareBundle.Tensor.FixedRestriction

noncomputable section

/-! Tensor comparison along a restriction fixed by a scheme endomorphism. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

open OAI.AlgebraicGeometry.Picard.PoincareBundle.Tensor.LinePullback

variable {X Y : Scheme.{u}} (p : X ⟶ Y) (g : Y ⟶ Y) (h : p ≫ g = p)

/-- The canonical comparison on a restriction fixed by the endomorphism. -/
def comparison (M : Y.Modules) :
    (Scheme.Modules.pullback p).obj ((Scheme.Modules.pullback g).obj M) ≅
      (Scheme.Modules.pullback p).obj M :=
  (Scheme.Modules.pullbackComp p g ≪≫ Scheme.Modules.pullbackCongr h).app M

/-- The fixed-restriction comparison respects the actual tensor product of line bundles. -/
theorem tensor_comparison (M N : Y.Modules)
    (hM : Line.Bundles.IsLine M) (hN : Line.Bundles.IsLine N) :
    (Scheme.Modules.pullback p).mapIso (LinePullback.pullbackIso g M N hM hN) ≪≫
      LinePullback.pullbackIso p ((Scheme.Modules.pullback g).obj M) ((Scheme.Modules.pullback g).obj N)
        (hM.pullback g) (hN.pullback g) ≪≫
      AbelianModuli.HilbertConstruction.Tensor.ProductSheaf.tensorModuleCongr (comparison p g h M) (comparison p g h N) =
    comparison p g h (AbelianModuli.HilbertConstruction.Tensor.ProductSheaf.tensorModule M N) ≪≫ LinePullback.pullbackIso p M N hM hN := by
  let CM := (Scheme.Modules.pullbackComp p g).app M
  let CN := (Scheme.Modules.pullbackComp p g).app N
  let CT := (Scheme.Modules.pullbackComp p g).app (AbelianModuli.HilbertConstruction.Tensor.ProductSheaf.tensorModule M N)
  let EM := (Scheme.Modules.pullbackCongr h).app M
  let EN := (Scheme.Modules.pullbackCongr h).app N
  let ET := (Scheme.Modules.pullbackCongr h).app (AbelianModuli.HilbertConstruction.Tensor.ProductSheaf.tensorModule M N)
  let D := (Scheme.Modules.pullback p).mapIso (LinePullback.pullbackIso g M N hM hN)
  let E := LinePullback.pullbackIso p ((Scheme.Modules.pullback g).obj M) ((Scheme.Modules.pullback g).obj N)
    (hM.pullback g) (hN.pullback g)
  let R := LinePullback.pullbackIso (p ≫ g) M N hM hN
  let U := AbelianModuli.HilbertConstruction.Tensor.ProductSheaf.tensorModuleCongr CM.symm CN.symm
  let V := AbelianModuli.HilbertConstruction.Tensor.ProductSheaf.tensorModuleCongr (comparison p g h M) (comparison p g h N)
  have hcomp : R ≪≫ U = CT.symm ≪≫ D ≪≫ E := LineIsoCoherence.composition p g M N hM hN
  have hcong : ET ≪≫ LinePullback.pullbackIso p M N hM hN = R ≪≫ AbelianModuli.HilbertConstruction.Tensor.ProductSheaf.tensorModuleCongr EM EN :=
    LineIsoCoherence.congr_map (p ≫ g) h M N hM hN
  have huv : U ≪≫ V = AbelianModuli.HilbertConstruction.Tensor.ProductSheaf.tensorModuleCongr EM EN := by
    change AbelianModuli.HilbertConstruction.Tensor.ProductSheaf.tensorModuleCongr CM.symm CN.symm ≪≫ AbelianModuli.HilbertConstruction.Tensor.ProductSheaf.tensorModuleCongr (CM ≪≫ EM) (CN ≪≫ EN) = _
    rw [CongrComposition.trans, Iso.symm_self_id_assoc, Iso.symm_self_id_assoc]
  change D ≪≫ E ≪≫ V = (CT ≪≫ ET) ≪≫ LinePullback.pullbackIso p M N hM hN
  calc
    D ≪≫ E ≪≫ V = CT ≪≫ (CT.symm ≪≫ D ≪≫ E) ≪≫ V := by
      simp only [Iso.trans_assoc, Iso.self_symm_id_assoc]
    _ = CT ≪≫ (R ≪≫ U) ≪≫ V := congrArg (fun q => CT ≪≫ q ≪≫ V) hcomp.symm
    _ = CT ≪≫ R ≪≫ AbelianModuli.HilbertConstruction.Tensor.ProductSheaf.tensorModuleCongr EM EN := by rw [Iso.trans_assoc, huv]
    _ = CT ≪≫ (ET ≪≫ LinePullback.pullbackIso p M N hM hN) := congrArg (fun q => CT ≪≫ q) hcong.symm
    _ = (CT ≪≫ ET) ≪≫ LinePullback.pullbackIso p M N hM hN := (Iso.trans_assoc _ _ _).symm

end

end OAI.AlgebraicGeometry.Picard.PoincareBundle.Tensor.FixedRestriction

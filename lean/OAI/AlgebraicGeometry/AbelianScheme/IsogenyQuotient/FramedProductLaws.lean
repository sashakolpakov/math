import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Poincare.BilinearProducts
import OAI.AlgebraicGeometry.Picard.PoincareBundle.Bilinear.InterchangeTransport

/-! # Framed Product Laws -/

namespace OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.FramedProductLaws.Construction

noncomputable section

/-! The normalized products at the origin satisfy the actual unit,
associativity and biextension interchange equations on sheaf sections. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

open OAI.AlgebraicGeometry.Picard.PoincareBundle.Tensor.UnitPullback

universe u

variable {S : Scheme.{u}}

theorem framedLineProduct_unit_left {M N : S.Modules}
    (l : AbelianModuli.HilbertConstruction.Line.Bundles.structureModule S ≅ M) (m : AbelianModuli.HilbertConstruction.Line.Bundles.structureModule S ≅ N)
    (U : S.Opens) (x : Γ(N, U)) :
    (Poincare.BilinearProducts.Construction.framedLineProduct l m m).app U (l.hom.app U (1 : Γ(S, U))) x = x := by
  have h := Picard.PoincareBundle.Bilinear.AlgebraTransport.unit_left (Picard.PoincareBundle.Tensor.UnitPullback.scalarBilinear (AbelianModuli.HilbertConstruction.Line.Bundles.structureModule S)) l m
    (𝟙 (AbelianModuli.HilbertConstruction.Line.Bundles.structureModule S)) (by
      intro V y
      change (1 : Γ(S, V)) • y = y
      exact one_smul _ _) U x
  simpa only [Category.id_comp, Poincare.BilinearProducts.Construction.framedLineProduct] using h

theorem framedLineProduct_unit_right {M N : S.Modules}
    (l : AbelianModuli.HilbertConstruction.Line.Bundles.structureModule S ≅ M) (m : AbelianModuli.HilbertConstruction.Line.Bundles.structureModule S ≅ N)
    (U : S.Opens) (x : Γ(M, U)) :
    (Poincare.BilinearProducts.Construction.framedLineProduct l m l).app U x (m.hom.app U (1 : Γ(S, U))) = x := by
  have h := Picard.PoincareBundle.Bilinear.AlgebraTransport.unit_right (Picard.PoincareBundle.Tensor.UnitPullback.scalarBilinear (AbelianModuli.HilbertConstruction.Line.Bundles.structureModule S)) l m
    (𝟙 (AbelianModuli.HilbertConstruction.Line.Bundles.structureModule S)) (by
      intro V y
      change Γ(S, V) at y
      change y * 1 = y
      exact mul_one _) U x
  simpa only [Category.id_comp, Poincare.BilinearProducts.Construction.framedLineProduct] using h

theorem framedLineProduct_associative {M N P MN NP R : S.Modules}
    (l : AbelianModuli.HilbertConstruction.Line.Bundles.structureModule S ≅ M) (m : AbelianModuli.HilbertConstruction.Line.Bundles.structureModule S ≅ N) (n : AbelianModuli.HilbertConstruction.Line.Bundles.structureModule S ≅ P)
    (lm : AbelianModuli.HilbertConstruction.Line.Bundles.structureModule S ≅ MN) (mn : AbelianModuli.HilbertConstruction.Line.Bundles.structureModule S ≅ NP) (r : AbelianModuli.HilbertConstruction.Line.Bundles.structureModule S ≅ R)
    (U : S.Opens) (x : Γ(M, U)) (y : Γ(N, U)) (z : Γ(P, U)) :
    (Poincare.BilinearProducts.Construction.framedLineProduct l mn r).app U x ((Poincare.BilinearProducts.Construction.framedLineProduct m n mn).app U y z) =
      (Poincare.BilinearProducts.Construction.framedLineProduct lm n r).app U ((Poincare.BilinearProducts.Construction.framedLineProduct l m lm).app U x y) z := by
  exact Picard.PoincareBundle.Bilinear.AlgebraTransport.associative
    (Picard.PoincareBundle.Tensor.UnitPullback.scalarBilinear (AbelianModuli.HilbertConstruction.Line.Bundles.structureModule S)) (Picard.PoincareBundle.Tensor.UnitPullback.scalarBilinear (AbelianModuli.HilbertConstruction.Line.Bundles.structureModule S))
    (Picard.PoincareBundle.Tensor.UnitPullback.scalarBilinear (AbelianModuli.HilbertConstruction.Line.Bundles.structureModule S)) (Picard.PoincareBundle.Tensor.UnitPullback.scalarBilinear (AbelianModuli.HilbertConstruction.Line.Bundles.structureModule S))
    l m n lm mn r (by
      intro V a b c
      change Γ(S, V) at a b c
      change a * (b * c) = (a * b) * c
      exact (mul_assoc _ _ _).symm) U x y z

theorem framedLineProduct_interchange {C A B X CA CB AX BX W : S.Modules}
    (ec : AbelianModuli.HilbertConstruction.Line.Bundles.structureModule S ≅ C) (ea : AbelianModuli.HilbertConstruction.Line.Bundles.structureModule S ≅ A)
    (eb : AbelianModuli.HilbertConstruction.Line.Bundles.structureModule S ≅ B) (ex : AbelianModuli.HilbertConstruction.Line.Bundles.structureModule S ≅ X)
    (eca : AbelianModuli.HilbertConstruction.Line.Bundles.structureModule S ≅ CA) (ecb : AbelianModuli.HilbertConstruction.Line.Bundles.structureModule S ≅ CB)
    (eax : AbelianModuli.HilbertConstruction.Line.Bundles.structureModule S ≅ AX) (ebx : AbelianModuli.HilbertConstruction.Line.Bundles.structureModule S ≅ BX) (ew : AbelianModuli.HilbertConstruction.Line.Bundles.structureModule S ≅ W)
    (U : S.Opens) (c : Γ(C, U)) (a : Γ(A, U)) (b : Γ(B, U)) (x : Γ(X, U)) :
    (Poincare.BilinearProducts.Construction.framedLineProduct ecb eax ew).app U ((Poincare.BilinearProducts.Construction.framedLineProduct ec eb ecb).app U c b)
      ((Poincare.BilinearProducts.Construction.framedLineProduct ea ex eax).app U a x) =
        (Poincare.BilinearProducts.Construction.framedLineProduct eca ebx ew).app U ((Poincare.BilinearProducts.Construction.framedLineProduct ec ea eca).app U c a)
          ((Poincare.BilinearProducts.Construction.framedLineProduct eb ex ebx).app U b x) := by
  exact Picard.PoincareBundle.Bilinear.InterchangeTransport.interchange
    (Picard.PoincareBundle.Tensor.UnitPullback.scalarBilinear (AbelianModuli.HilbertConstruction.Line.Bundles.structureModule S)) (Picard.PoincareBundle.Tensor.UnitPullback.scalarBilinear (AbelianModuli.HilbertConstruction.Line.Bundles.structureModule S))
    (Picard.PoincareBundle.Tensor.UnitPullback.scalarBilinear (AbelianModuli.HilbertConstruction.Line.Bundles.structureModule S)) (Picard.PoincareBundle.Tensor.UnitPullback.scalarBilinear (AbelianModuli.HilbertConstruction.Line.Bundles.structureModule S))
    (Picard.PoincareBundle.Tensor.UnitPullback.scalarBilinear (AbelianModuli.HilbertConstruction.Line.Bundles.structureModule S)) (Picard.PoincareBundle.Tensor.UnitPullback.scalarBilinear (AbelianModuli.HilbertConstruction.Line.Bundles.structureModule S))
    ec ea eb ex eca ecb eax ebx ew (by
      intro V c a b x
      change Γ(S, V) at c a b x
      change (c * b) * (a * x) = (c * a) * (b * x)
      exact mul_mul_mul_comm _ _ _ _) U c a b x

end

end OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.FramedProductLaws.Construction

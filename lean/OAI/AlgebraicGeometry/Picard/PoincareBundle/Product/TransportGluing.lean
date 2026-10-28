import OAI.AlgebraicGeometry.Picard.PoincareBundle.QuotientBilinearEquivariance
import OAI.AlgebraicGeometry.Picard.PoincareBundle.Product.ParameterSchemes
import OAI.AlgebraicGeometry.Picard.PoincareBundle.FiberBilinearGluing

/-! # Transport Gluing -/

namespace OAI.AlgebraicGeometry.Picard.PoincareBundle.Product.TransportGluing

noncomputable section

/-!
# The universal horizontal sheaf product respects its genuine quotient transports
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory

universe u

open OAI.AlgebraicGeometry.Picard.PoincareBundle.FiberwiseMultiplication OAI.AlgebraicGeometry.Picard.PoincareBundle.Line.Fibers OAI.AlgebraicGeometry.Picard.PoincareBundle.Product.ParameterSchemes
open OAI.AlgebraicGeometry.Picard.PoincareBundle.Biextension.AxisData OAI.AlgebraicGeometry.Picard.PoincareBundle.Geometric.KernelLinearization OAI.AlgebraicGeometry.Picard.PoincareBundle.FiberBilinearGluing

/-- Equal cover images remain equal after a genuine commuting square. -/
theorem square_images {C : Type*} [Category C] {A B A' B' T : C}
    (f : A ⟶ B) (f' : A' ⟶ B') (i : A' ⟶ A) (j : B' ⟶ B)
    (hi : f' ≫ j = i ≫ f) (p q : T ⟶ A') (h : p ≫ f' = q ≫ f') :
    (p ≫ i) ≫ f = (q ≫ i) ≫ f := by
  rw [Category.assoc, ← hi, ← Category.assoc, h, Category.assoc, hi, ← Category.assoc]

variable {S : Scheme.{u}} {A B X Y : Over S}
  [GrpObj A] [IsCommMonObj A] [GrpObj B] [GrpObj X] [IsCommMonObj X] [GrpObj Y]
  (f : A ⟶ B) (g : X ⟶ Y) [IsMonHom f] [IsMonHom g]
  (L : Line.Bundles.LineBundle (A ⊗ X).left)
  (Dh : FiberwiseMultiplication.Multiplication (fst A X) (snd A X) L) (Dv : FiberwiseMultiplication.Multiplication (snd A X) (fst A X) L)
  (Kh : FiberwiseMultiplication.KernelFrames (fst A X) (snd A X) L f Dh) (Kv : FiberwiseMultiplication.KernelFrames (snd A X) (fst A X) L g Dv)

omit [IsCommMonObj A] [IsCommMonObj X] in
/-- The actual quotient transport, expressed between the two pulled-back universal input or output sheaves. -/
def productTransport {T : Over S} (p q : T ⟶ (A ⊗ A) ⊗ X) (i : (A ⊗ A) ⊗ X ⟶ A ⊗ X)
    (h : (p ≫ i) ≫ (f ⊗ₘ g) = (q ≫ i) ≫ (f ⊗ₘ g)) :
    (Scheme.Modules.pullback p.left).obj (Line.Fibers.fiber L i) ⟶ (Scheme.Modules.pullback q.left).obj (Line.Fibers.fiber L i) :=
  FiberBilinearGluing.fiberTransport L p q i
    (RectangularTransport.total f g (Geometric.KernelLinearization.overModulePullbacks S) L.sheaf
      (Biextension.AxisData.toAxisData f g L Dh Dv Kh Kv) (p ≫ i) (q ≫ i) h)

variable (hi : Biextension.Compatibility.Interchange L Dh Dv)
  (hc : KernelFrame.Centrality.Central f Kh) (ht : Kernel.FramesTransverseTransport.Transverse g Kv Dh)

include hi hc ht in
/-- The universal product satisfies its full geometric bilinear gluing equation on every test scheme. -/
theorem horizontal_equivariance {T : Over S} (p q : T ⟶ (A ⊗ A) ⊗ X)
    (h : p ≫ ((f ⊗ₘ f) ⊗ₘ g) = q ≫ ((f ⊗ₘ f) ⊗ₘ g)) :
    (Bilinear.BilinearPullback.pullback q.left (Line.Fibers.fiber_isLine L (ParameterSchemes.inputLeft A X))
      (Line.Fibers.fiber_isLine L (ParameterSchemes.inputRight A X)) (ParameterSchemes.globalProduct A X L Dh)).precomp
        (productTransport f g L Dh Dv Kh Kv p q (ParameterSchemes.inputLeft A X)
          (square_images _ _ _ _ (ParameterSchemes.inputLeft_naturality f g) p q h))
        (productTransport f g L Dh Dv Kh Kv p q (ParameterSchemes.inputRight A X)
          (square_images _ _ _ _ (ParameterSchemes.inputRight_naturality f g) p q h)) =
    (Bilinear.BilinearPullback.pullback p.left (Line.Fibers.fiber_isLine L (ParameterSchemes.inputLeft A X))
      (Line.Fibers.fiber_isLine L (ParameterSchemes.inputRight A X)) (ParameterSchemes.globalProduct A X L Dh)).postcomp
        (productTransport f g L Dh Dv Kh Kv p q (ParameterSchemes.outputPoint A X)
          (square_images _ _ _ _ (ParameterSchemes.outputPoint_naturality f g) p q h)) := by
  apply FiberBilinearGluing.equivariance_of_fibers
  rw [ParameterSchemes.globalProduct_pullback, ParameterSchemes.globalProduct_pullback]
  exact QuotientBilinearEquivariance.horizontal_bilinear f g L Dh Dv Kh Kv hi hc ht
    _ _ _ _ _ _ (ParameterSchemes.parameterRelation A X p) (ParameterSchemes.parameterRelation A X q) _ _ _

end

end OAI.AlgebraicGeometry.Picard.PoincareBundle.Product.TransportGluing

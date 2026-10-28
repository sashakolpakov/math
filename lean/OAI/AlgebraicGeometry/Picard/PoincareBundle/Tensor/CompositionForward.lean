import OAI.AlgebraicGeometry.Picard.PoincareBundle.Tensor.LineIsoCoherence
import OAI.AlgebraicGeometry.Picard.PoincareBundle.Tensor.CongrComposition
import OAI.AlgebraicGeometry.Picard.PoincareBundle.TripleTensorFactorSwap

/-! # Composition Forward -/

namespace OAI.AlgebraicGeometry.Picard.PoincareBundle.Tensor.CompositionForward

noncomputable section

/-! The tensor pullback composition law with the composite comparison on the right. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

open OAI.AlgebraicGeometry.Picard.PoincareBundle.Tensor.LinePullback

theorem move_inverse {C : Type*} [Category C] {A B D E F : C}
    (r : A ≅ B) (u : B ≅ D) (c : E ≅ A) (v : E ≅ F) (w : F ≅ D)
    (h : r ≪≫ u = c.symm ≪≫ v ≪≫ w) :
    v ≪≫ w ≪≫ u.symm = c ≪≫ r := by
  have hh := congrArg (fun e => c ≪≫ e ≪≫ u.symm) h
  simpa only [Iso.trans_assoc, Iso.self_symm_id_assoc, Iso.self_symm_id, Iso.trans_refl] using hh.symm

theorem tensor_inverse {X : Scheme.{u}} {M M' N N' : X.Modules} (a : M ≅ M') (b : N ≅ N') :
    (AbelianModuli.HilbertConstruction.Tensor.ProductSheaf.tensorModuleCongr a.symm b.symm).symm = AbelianModuli.HilbertConstruction.Tensor.ProductSheaf.tensorModuleCongr a b := by
  apply Iso.ext
  rfl

theorem composition {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) (M N : Z.Modules)
    (hM : Line.Bundles.IsLine M) (hN : Line.Bundles.IsLine N) :
    (Scheme.Modules.pullback f).mapIso (LinePullback.pullbackIso g M N hM hN) ≪≫
      LinePullback.pullbackIso f ((Scheme.Modules.pullback g).obj M) ((Scheme.Modules.pullback g).obj N)
        (hM.pullback g) (hN.pullback g) ≪≫
      AbelianModuli.HilbertConstruction.Tensor.ProductSheaf.tensorModuleCongr ((Scheme.Modules.pullbackComp f g).app M) ((Scheme.Modules.pullbackComp f g).app N) =
    (Scheme.Modules.pullbackComp f g).app (AbelianModuli.HilbertConstruction.Tensor.ProductSheaf.tensorModule M N) ≪≫ LinePullback.pullbackIso (f ≫ g) M N hM hN := by
  have h := move_inverse (LinePullback.pullbackIso (f ≫ g) M N hM hN)
    (AbelianModuli.HilbertConstruction.Tensor.ProductSheaf.tensorModuleCongr ((Scheme.Modules.pullbackComp f g).app M).symm
      ((Scheme.Modules.pullbackComp f g).app N).symm)
    ((Scheme.Modules.pullbackComp f g).app (AbelianModuli.HilbertConstruction.Tensor.ProductSheaf.tensorModule M N))
    ((Scheme.Modules.pullback f).mapIso (LinePullback.pullbackIso g M N hM hN))
    (LinePullback.pullbackIso f ((Scheme.Modules.pullback g).obj M) ((Scheme.Modules.pullback g).obj N)
      (hM.pullback g) (hN.pullback g))
    (LineIsoCoherence.composition f g M N hM hN)
  rw [tensor_inverse] at h
  exact h

end

end OAI.AlgebraicGeometry.Picard.PoincareBundle.Tensor.CompositionForward

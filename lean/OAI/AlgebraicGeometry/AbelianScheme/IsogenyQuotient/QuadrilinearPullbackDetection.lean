import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.TensorFourPullback

/-! # Quadrilinear Pullback Detection -/

namespace OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.QuadrilinearPullbackDetection.Construction

noncomputable section

/-! The four pullback units jointly detect actual four-linear maps
on the geometric pullbacks of line sheaves. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

set_option backward.isDefEq.respectTransparency false in
theorem quadrilinear_eq_of_pullback_units {X Y : Scheme.{u}} (f : X ⟶ Y) (M N P Q : Y.Modules)
    (hM : Picard.PoincareBundle.Line.Bundles.IsLine M) (hN : Picard.PoincareBundle.Line.Bundles.IsLine N)
    (hP : Picard.PoincareBundle.Line.Bundles.IsLine P) (hQ : Picard.PoincareBundle.Line.Bundles.IsLine Q) {R : X.Modules}
    (b c : QuadrilinearProducts.Construction.SheafQuadrilinearMap ((Scheme.Modules.pullback f).obj M) ((Scheme.Modules.pullback f).obj N)
      ((Scheme.Modules.pullback f).obj P) ((Scheme.Modules.pullback f).obj Q) R)
    (h : ∀ (U : Y.Opens) (m : Γ(M, U)) (n : Γ(N, U)) (p : Γ(P, U)) (q : Γ(Q, U)),
      b.app (f ⁻¹ᵁ U) ((TensorTriplePullback.Construction.linePullbackUnit f M).app U m) ((TensorTriplePullback.Construction.linePullbackUnit f N).app U n)
        ((TensorTriplePullback.Construction.linePullbackUnit f P).app U p) ((TensorTriplePullback.Construction.linePullbackUnit f Q).app U q) =
      c.app (f ⁻¹ᵁ U) ((TensorTriplePullback.Construction.linePullbackUnit f M).app U m) ((TensorTriplePullback.Construction.linePullbackUnit f N).app U n)
        ((TensorTriplePullback.Construction.linePullbackUnit f P).app U p) ((TensorTriplePullback.Construction.linePullbackUnit f Q).app U q)) : b = c := by
  have : IsIso (TensorFourPullback.Construction.tensorFourPullbackMap f M N P Q) := TensorFourPullback.Construction.tensorFourPullbackMap_isIso f M N P Q hM hN hP hQ
  apply (TensorQuadrilinear.Construction.tensorQuadrilinearEquiv _ _ _ _ R).symm.injective
  apply (cancel_epi (TensorFourPullback.Construction.tensorFourPullbackMap f M N P Q)).mp
  apply ((Scheme.Modules.pullbackPushforwardAdjunction f).homEquiv _ _).injective
  apply (TensorQuadrilinear.Construction.tensorQuadrilinearEquiv M N P Q _).injective
  rw [Adjunction.homEquiv_unit, Adjunction.homEquiv_unit]
  ext U m n p q
  rw [TensorQuadrilinear.Construction.tensorQuadrilinearEquiv_apply, TensorQuadrilinear.Construction.tensorQuadrilinearEquiv_apply]
  change ((TensorQuadrilinear.Construction.tensorQuadrilinearEquiv _ _ _ _ R).symm b).app (f ⁻¹ᵁ U)
      ((TensorFourPullback.Construction.tensorFourPullbackMap f M N P Q).app (f ⁻¹ᵁ U)
        ((TensorTriplePullback.Construction.linePullbackUnit f (AbelianModuli.HilbertConstruction.Tensor.ProductSheaf.tensorModule (AbelianModuli.HilbertConstruction.Tensor.ProductSheaf.tensorModule (AbelianModuli.HilbertConstruction.Tensor.ProductSheaf.tensorModule M N) P) Q)).app U
          ((Picard.Homomorphisms.TensorAssociativity.Construction.tensorModuleBilinear (AbelianModuli.HilbertConstruction.Tensor.ProductSheaf.tensorModule (AbelianModuli.HilbertConstruction.Tensor.ProductSheaf.tensorModule M N) P) Q).app U
            ((Picard.Homomorphisms.TensorAssociativity.Construction.tensorModuleBilinear (AbelianModuli.HilbertConstruction.Tensor.ProductSheaf.tensorModule M N) P).app U ((Picard.Homomorphisms.TensorAssociativity.Construction.tensorModuleBilinear M N).app U m n) p) q))) =
    ((TensorQuadrilinear.Construction.tensorQuadrilinearEquiv _ _ _ _ R).symm c).app (f ⁻¹ᵁ U)
      ((TensorFourPullback.Construction.tensorFourPullbackMap f M N P Q).app (f ⁻¹ᵁ U)
        ((TensorTriplePullback.Construction.linePullbackUnit f (AbelianModuli.HilbertConstruction.Tensor.ProductSheaf.tensorModule (AbelianModuli.HilbertConstruction.Tensor.ProductSheaf.tensorModule (AbelianModuli.HilbertConstruction.Tensor.ProductSheaf.tensorModule M N) P) Q)).app U
          ((Picard.Homomorphisms.TensorAssociativity.Construction.tensorModuleBilinear (AbelianModuli.HilbertConstruction.Tensor.ProductSheaf.tensorModule (AbelianModuli.HilbertConstruction.Tensor.ProductSheaf.tensorModule M N) P) Q).app U
            ((Picard.Homomorphisms.TensorAssociativity.Construction.tensorModuleBilinear (AbelianModuli.HilbertConstruction.Tensor.ProductSheaf.tensorModule M N) P).app U ((Picard.Homomorphisms.TensorAssociativity.Construction.tensorModuleBilinear M N).app U m n) p) q)))
  rw [TensorFourPullback.Construction.tensorFourPullbackMap_app_unit, ← TensorQuadrilinear.Construction.tensorQuadrilinearEquiv_apply, ← TensorQuadrilinear.Construction.tensorQuadrilinearEquiv_apply,
    Equiv.apply_symm_apply, Equiv.apply_symm_apply]
  exact h U m n p q

end

end OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.QuadrilinearPullbackDetection.Construction

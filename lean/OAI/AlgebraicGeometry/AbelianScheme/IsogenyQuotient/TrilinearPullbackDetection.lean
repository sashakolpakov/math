import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.TensorTriplePullback

/-! # Trilinear Pullback Detection -/

namespace OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.TrilinearPullbackDetection.Construction

noncomputable section

/-! The pullback units jointly detect trilinear maps on actual pulled
back line sheaves. This is the three-input tensor adjunction. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

open OAI.AlgebraicGeometry.Picard.PoincareBundle.Tensor.PullbackMap

universe u

variable {X Y : Scheme.{u}} (f : X ⟶ Y)

set_option backward.isDefEq.respectTransparency false in
theorem trilinear_eq_of_pullback_units (M N P : Y.Modules)
    (hM : Picard.PoincareBundle.Line.Bundles.IsLine M) (hN : Picard.PoincareBundle.Line.Bundles.IsLine N) (hP : Picard.PoincareBundle.Line.Bundles.IsLine P)
    {Q : X.Modules}
    (b c : Picard.Homomorphisms.Trilinear.Construction.SheafTrilinearMap ((Scheme.Modules.pullback f).obj M)
      ((Scheme.Modules.pullback f).obj N) ((Scheme.Modules.pullback f).obj P) Q)
    (h : ∀ (U : Y.Opens) (m : Γ(M, U)) (n : Γ(N, U)) (p : Γ(P, U)),
      b.app (f ⁻¹ᵁ U) ((TensorTriplePullback.Construction.linePullbackUnit f M).app U m) ((TensorTriplePullback.Construction.linePullbackUnit f N).app U n)
        ((TensorTriplePullback.Construction.linePullbackUnit f P).app U p) =
      c.app (f ⁻¹ᵁ U) ((TensorTriplePullback.Construction.linePullbackUnit f M).app U m) ((TensorTriplePullback.Construction.linePullbackUnit f N).app U n)
        ((TensorTriplePullback.Construction.linePullbackUnit f P).app U p)) : b = c := by
  have : IsIso (TensorTriplePullback.Construction.tensorTriplePullbackMap f M N P) := TensorTriplePullback.Construction.tensorTriplePullbackMap_isIso f M N P hM hN hP
  apply (Picard.Homomorphisms.TensorAssociativity.Construction.tensorLeftTrilinearEquiv _ _ _ Q).symm.injective
  apply (cancel_epi (TensorTriplePullback.Construction.tensorTriplePullbackMap f M N P)).mp
  apply ((Scheme.Modules.pullbackPushforwardAdjunction f).homEquiv _ _).injective
  apply (Picard.Homomorphisms.TensorAssociativity.Construction.tensorLeftTrilinearEquiv M N P _).injective
  rw [Adjunction.homEquiv_unit, Adjunction.homEquiv_unit]
  ext U m n p
  rw [Picard.Homomorphisms.TensorAssociativity.Construction.tensorLeftTrilinearEquiv_apply, Picard.Homomorphisms.TensorAssociativity.Construction.tensorLeftTrilinearEquiv_apply]
  change ((Picard.Homomorphisms.TensorAssociativity.Construction.tensorLeftTrilinearEquiv _ _ _ Q).symm b).app (f ⁻¹ᵁ U)
      ((TensorTriplePullback.Construction.tensorTriplePullbackMap f M N P).app (f ⁻¹ᵁ U)
        ((TensorTriplePullback.Construction.linePullbackUnit f (AbelianModuli.HilbertConstruction.Tensor.ProductSheaf.tensorModule (AbelianModuli.HilbertConstruction.Tensor.ProductSheaf.tensorModule M N) P)).app U
          ((Picard.Homomorphisms.TensorAssociativity.Construction.tensorModuleBilinear (AbelianModuli.HilbertConstruction.Tensor.ProductSheaf.tensorModule M N) P).app U ((Picard.Homomorphisms.TensorAssociativity.Construction.tensorModuleBilinear M N).app U m n) p))) =
    ((Picard.Homomorphisms.TensorAssociativity.Construction.tensorLeftTrilinearEquiv _ _ _ Q).symm c).app (f ⁻¹ᵁ U)
      ((TensorTriplePullback.Construction.tensorTriplePullbackMap f M N P).app (f ⁻¹ᵁ U)
        ((TensorTriplePullback.Construction.linePullbackUnit f (AbelianModuli.HilbertConstruction.Tensor.ProductSheaf.tensorModule (AbelianModuli.HilbertConstruction.Tensor.ProductSheaf.tensorModule M N) P)).app U
          ((Picard.Homomorphisms.TensorAssociativity.Construction.tensorModuleBilinear (AbelianModuli.HilbertConstruction.Tensor.ProductSheaf.tensorModule M N) P).app U ((Picard.Homomorphisms.TensorAssociativity.Construction.tensorModuleBilinear M N).app U m n) p)))
  rw [TensorTriplePullback.Construction.tensorTriplePullbackMap_app_unit,
    ← Picard.Homomorphisms.TensorAssociativity.Construction.tensorLeftTrilinearEquiv_apply, ← Picard.Homomorphisms.TensorAssociativity.Construction.tensorLeftTrilinearEquiv_apply,
    Equiv.apply_symm_apply, Equiv.apply_symm_apply]
  exact h U m n p

theorem bilinearPullback_app_units {M N P : Y.Modules}
    (hM : Picard.PoincareBundle.Line.Bundles.IsLine M) (hN : Picard.PoincareBundle.Line.Bundles.IsLine N) (b : AbelianModuli.HilbertConstruction.Bilinear.Sheaves.SheafBilinearMap M N P)
    (U : Y.Opens) (m : Γ(M, U)) (n : Γ(N, U)) :
    (Picard.PoincareBundle.Bilinear.BilinearPullback.pullback f hM hN b).app (f ⁻¹ᵁ U)
      ((TensorTriplePullback.Construction.linePullbackUnit f M).app U m) ((TensorTriplePullback.Construction.linePullbackUnit f N).app U n) =
        (TensorTriplePullback.Construction.linePullbackUnit f P).app U (b.app U m n) :=
  congrArg (fun b => b.app U m n) (BilinearPullbackAdjunction.Construction.bilinearAdjoint_pullback f M N hM hN b)

end

end OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.TrilinearPullbackDetection.Construction

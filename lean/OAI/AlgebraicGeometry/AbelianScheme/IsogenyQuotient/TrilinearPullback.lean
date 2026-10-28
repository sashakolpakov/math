import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.TrilinearPullbackDetection

/-! # Trilinear Pullback -/

namespace OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.TrilinearPullback.Construction

noncomputable section

/-! Geometric pullback of actual trilinear maps between line sheaves,
constructed through the tensor adjunction and characterized on units. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

variable {X Y : Scheme.{u}} {M N P Q : Y.Modules}

def lineTrilinearToHom (b : Picard.Homomorphisms.Trilinear.Construction.SheafTrilinearMap M N P Q) : AbelianModuli.HilbertConstruction.Tensor.ProductSheaf.tensorModule (AbelianModuli.HilbertConstruction.Tensor.ProductSheaf.tensorModule M N) P ⟶ Q :=
  (Picard.Homomorphisms.TensorAssociativity.Construction.tensorLeftTrilinearEquiv M N P Q).symm b

theorem lineTrilinearToHom_app_tensor (b : Picard.Homomorphisms.Trilinear.Construction.SheafTrilinearMap M N P Q)
    (U : Y.Opens) (m : Γ(M, U)) (n : Γ(N, U)) (p : Γ(P, U)) :
    (lineTrilinearToHom b).app U
      ((Picard.Homomorphisms.TensorAssociativity.Construction.tensorModuleBilinear (AbelianModuli.HilbertConstruction.Tensor.ProductSheaf.tensorModule M N) P).app U ((Picard.Homomorphisms.TensorAssociativity.Construction.tensorModuleBilinear M N).app U m n) p) =
        b.app U m n p := by
  rw [← Picard.Homomorphisms.TensorAssociativity.Construction.tensorLeftTrilinearEquiv_apply]
  exact congrArg (fun b => b.app U m n p) ((Picard.Homomorphisms.TensorAssociativity.Construction.tensorLeftTrilinearEquiv M N P Q).apply_symm_apply b)

def tensorTriplePullbackIso (f : X ⟶ Y) (M N P : Y.Modules)
    (hM : Picard.PoincareBundle.Line.Bundles.IsLine M) (hN : Picard.PoincareBundle.Line.Bundles.IsLine N) (hP : Picard.PoincareBundle.Line.Bundles.IsLine P) :
    (Scheme.Modules.pullback f).obj (AbelianModuli.HilbertConstruction.Tensor.ProductSheaf.tensorModule (AbelianModuli.HilbertConstruction.Tensor.ProductSheaf.tensorModule M N) P) ≅
      AbelianModuli.HilbertConstruction.Tensor.ProductSheaf.tensorModule (AbelianModuli.HilbertConstruction.Tensor.ProductSheaf.tensorModule ((Scheme.Modules.pullback f).obj M) ((Scheme.Modules.pullback f).obj N))
        ((Scheme.Modules.pullback f).obj P) := by
  have : IsIso (TensorTriplePullback.Construction.tensorTriplePullbackMap f M N P) := TensorTriplePullback.Construction.tensorTriplePullbackMap_isIso f M N P hM hN hP
  exact asIso (TensorTriplePullback.Construction.tensorTriplePullbackMap f M N P)

def lineTrilinearPulledHom (f : X ⟶ Y)
    (hM : Picard.PoincareBundle.Line.Bundles.IsLine M) (hN : Picard.PoincareBundle.Line.Bundles.IsLine N) (hP : Picard.PoincareBundle.Line.Bundles.IsLine P)
    (b : Picard.Homomorphisms.Trilinear.Construction.SheafTrilinearMap M N P Q) :
    AbelianModuli.HilbertConstruction.Tensor.ProductSheaf.tensorModule (AbelianModuli.HilbertConstruction.Tensor.ProductSheaf.tensorModule ((Scheme.Modules.pullback f).obj M) ((Scheme.Modules.pullback f).obj N))
      ((Scheme.Modules.pullback f).obj P) ⟶ (Scheme.Modules.pullback f).obj Q :=
  (tensorTriplePullbackIso f M N P hM hN hP).inv ≫ (Scheme.Modules.pullback f).map (lineTrilinearToHom b)

theorem lineTrilinearPulledHom_fac (f : X ⟶ Y)
    (hM : Picard.PoincareBundle.Line.Bundles.IsLine M) (hN : Picard.PoincareBundle.Line.Bundles.IsLine N) (hP : Picard.PoincareBundle.Line.Bundles.IsLine P)
    (b : Picard.Homomorphisms.Trilinear.Construction.SheafTrilinearMap M N P Q) :
    TensorTriplePullback.Construction.tensorTriplePullbackMap f M N P ≫ lineTrilinearPulledHom f hM hN hP b =
      (Scheme.Modules.pullback f).map (lineTrilinearToHom b) := by
  change (tensorTriplePullbackIso f M N P hM hN hP).hom ≫
    (tensorTriplePullbackIso f M N P hM hN hP).inv ≫ _ = _
  exact Iso.hom_inv_id_assoc _ _

def lineTrilinearPullback (f : X ⟶ Y)
    (hM : Picard.PoincareBundle.Line.Bundles.IsLine M) (hN : Picard.PoincareBundle.Line.Bundles.IsLine N) (hP : Picard.PoincareBundle.Line.Bundles.IsLine P)
    (b : Picard.Homomorphisms.Trilinear.Construction.SheafTrilinearMap M N P Q) :
    Picard.Homomorphisms.Trilinear.Construction.SheafTrilinearMap ((Scheme.Modules.pullback f).obj M) ((Scheme.Modules.pullback f).obj N)
      ((Scheme.Modules.pullback f).obj P) ((Scheme.Modules.pullback f).obj Q) :=
  Picard.Homomorphisms.TensorAssociativity.Construction.tensorLeftTrilinearEquiv _ _ _ _ (lineTrilinearPulledHom f hM hN hP b)

theorem lineTrilinearPullback_app_units (f : X ⟶ Y)
    (hM : Picard.PoincareBundle.Line.Bundles.IsLine M) (hN : Picard.PoincareBundle.Line.Bundles.IsLine N) (hP : Picard.PoincareBundle.Line.Bundles.IsLine P)
    (b : Picard.Homomorphisms.Trilinear.Construction.SheafTrilinearMap M N P Q)
    (U : Y.Opens) (m : Γ(M, U)) (n : Γ(N, U)) (p : Γ(P, U)) :
    (lineTrilinearPullback f hM hN hP b).app (f ⁻¹ᵁ U)
      ((TensorTriplePullback.Construction.linePullbackUnit f M).app U m) ((TensorTriplePullback.Construction.linePullbackUnit f N).app U n) ((TensorTriplePullback.Construction.linePullbackUnit f P).app U p) =
        (TensorTriplePullback.Construction.linePullbackUnit f Q).app U (b.app U m n p) := by
  have h := congrArg (fun a => a.app (f ⁻¹ᵁ U)
    ((TensorTriplePullback.Construction.linePullbackUnit f (AbelianModuli.HilbertConstruction.Tensor.ProductSheaf.tensorModule (AbelianModuli.HilbertConstruction.Tensor.ProductSheaf.tensorModule M N) P)).app U
      ((Picard.Homomorphisms.TensorAssociativity.Construction.tensorModuleBilinear (AbelianModuli.HilbertConstruction.Tensor.ProductSheaf.tensorModule M N) P).app U ((Picard.Homomorphisms.TensorAssociativity.Construction.tensorModuleBilinear M N).app U m n) p)))
        (lineTrilinearPulledHom_fac f hM hN hP b)
  change (lineTrilinearPulledHom f hM hN hP b).app (f ⁻¹ᵁ U)
    ((TensorTriplePullback.Construction.tensorTriplePullbackMap f M N P).app (f ⁻¹ᵁ U) _) = _ at h
  rw [TensorTriplePullback.Construction.tensorTriplePullbackMap_app_unit, TensorTriplePullback.Construction.linePullbackUnit_natural, lineTrilinearToHom_app_tensor] at h
  exact (Picard.Homomorphisms.TensorAssociativity.Construction.tensorLeftTrilinearEquiv_apply _ _ _ _ _).trans h

end

end OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.TrilinearPullback.Construction

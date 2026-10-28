import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.QuadrilinearPullbackDetection

/-! # Quadrilinear Pullback -/

namespace OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.QuadrilinearPullback.Construction

noncomputable section

/-! Actual geometric pullback of four-linear line-sheaf maps,
characterized by its four adjunction-unit inputs. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

variable {X Y : Scheme.{u}} {M N P Q R : Y.Modules}

def tensorFourPullbackIso (f : X ⟶ Y) (M N P Q : Y.Modules)
    (hM : Picard.PoincareBundle.Line.Bundles.IsLine M) (hN : Picard.PoincareBundle.Line.Bundles.IsLine N)
    (hP : Picard.PoincareBundle.Line.Bundles.IsLine P) (hQ : Picard.PoincareBundle.Line.Bundles.IsLine Q) :
    (Scheme.Modules.pullback f).obj (AbelianModuli.HilbertConstruction.Tensor.ProductSheaf.tensorModule (AbelianModuli.HilbertConstruction.Tensor.ProductSheaf.tensorModule (AbelianModuli.HilbertConstruction.Tensor.ProductSheaf.tensorModule M N) P) Q) ≅
      AbelianModuli.HilbertConstruction.Tensor.ProductSheaf.tensorModule (AbelianModuli.HilbertConstruction.Tensor.ProductSheaf.tensorModule (AbelianModuli.HilbertConstruction.Tensor.ProductSheaf.tensorModule ((Scheme.Modules.pullback f).obj M)
        ((Scheme.Modules.pullback f).obj N)) ((Scheme.Modules.pullback f).obj P)) ((Scheme.Modules.pullback f).obj Q) := by
  have : IsIso (TensorFourPullback.Construction.tensorFourPullbackMap f M N P Q) := TensorFourPullback.Construction.tensorFourPullbackMap_isIso f M N P Q hM hN hP hQ
  exact asIso (TensorFourPullback.Construction.tensorFourPullbackMap f M N P Q)

def lineQuadrilinearPulledHom (f : X ⟶ Y)
    (hM : Picard.PoincareBundle.Line.Bundles.IsLine M) (hN : Picard.PoincareBundle.Line.Bundles.IsLine N)
    (hP : Picard.PoincareBundle.Line.Bundles.IsLine P) (hQ : Picard.PoincareBundle.Line.Bundles.IsLine Q) (b : QuadrilinearProducts.Construction.SheafQuadrilinearMap M N P Q R) :
    AbelianModuli.HilbertConstruction.Tensor.ProductSheaf.tensorModule (AbelianModuli.HilbertConstruction.Tensor.ProductSheaf.tensorModule (AbelianModuli.HilbertConstruction.Tensor.ProductSheaf.tensorModule ((Scheme.Modules.pullback f).obj M)
      ((Scheme.Modules.pullback f).obj N)) ((Scheme.Modules.pullback f).obj P)) ((Scheme.Modules.pullback f).obj Q) ⟶
        (Scheme.Modules.pullback f).obj R :=
  (tensorFourPullbackIso f M N P Q hM hN hP hQ).inv ≫ (Scheme.Modules.pullback f).map (TensorQuadrilinear.Construction.lineQuadrilinearToHom b)

theorem lineQuadrilinearPulledHom_fac (f : X ⟶ Y)
    (hM : Picard.PoincareBundle.Line.Bundles.IsLine M) (hN : Picard.PoincareBundle.Line.Bundles.IsLine N)
    (hP : Picard.PoincareBundle.Line.Bundles.IsLine P) (hQ : Picard.PoincareBundle.Line.Bundles.IsLine Q) (b : QuadrilinearProducts.Construction.SheafQuadrilinearMap M N P Q R) :
    TensorFourPullback.Construction.tensorFourPullbackMap f M N P Q ≫ lineQuadrilinearPulledHom f hM hN hP hQ b =
      (Scheme.Modules.pullback f).map (TensorQuadrilinear.Construction.lineQuadrilinearToHom b) := by
  change (tensorFourPullbackIso f M N P Q hM hN hP hQ).hom ≫
    (tensorFourPullbackIso f M N P Q hM hN hP hQ).inv ≫ _ = _
  exact Iso.hom_inv_id_assoc _ _

def lineQuadrilinearPullback (f : X ⟶ Y)
    (hM : Picard.PoincareBundle.Line.Bundles.IsLine M) (hN : Picard.PoincareBundle.Line.Bundles.IsLine N)
    (hP : Picard.PoincareBundle.Line.Bundles.IsLine P) (hQ : Picard.PoincareBundle.Line.Bundles.IsLine Q) (b : QuadrilinearProducts.Construction.SheafQuadrilinearMap M N P Q R) :
    QuadrilinearProducts.Construction.SheafQuadrilinearMap ((Scheme.Modules.pullback f).obj M) ((Scheme.Modules.pullback f).obj N)
      ((Scheme.Modules.pullback f).obj P) ((Scheme.Modules.pullback f).obj Q) ((Scheme.Modules.pullback f).obj R) :=
  TensorQuadrilinear.Construction.tensorQuadrilinearEquiv _ _ _ _ _ (lineQuadrilinearPulledHom f hM hN hP hQ b)

theorem lineQuadrilinearPullback_app_units (f : X ⟶ Y)
    (hM : Picard.PoincareBundle.Line.Bundles.IsLine M) (hN : Picard.PoincareBundle.Line.Bundles.IsLine N)
    (hP : Picard.PoincareBundle.Line.Bundles.IsLine P) (hQ : Picard.PoincareBundle.Line.Bundles.IsLine Q) (b : QuadrilinearProducts.Construction.SheafQuadrilinearMap M N P Q R)
    (U : Y.Opens) (m : Γ(M, U)) (n : Γ(N, U)) (p : Γ(P, U)) (q : Γ(Q, U)) :
    (lineQuadrilinearPullback f hM hN hP hQ b).app (f ⁻¹ᵁ U)
      ((TensorTriplePullback.Construction.linePullbackUnit f M).app U m) ((TensorTriplePullback.Construction.linePullbackUnit f N).app U n)
      ((TensorTriplePullback.Construction.linePullbackUnit f P).app U p) ((TensorTriplePullback.Construction.linePullbackUnit f Q).app U q) =
        (TensorTriplePullback.Construction.linePullbackUnit f R).app U (b.app U m n p q) := by
  have h := congrArg (fun a => a.app (f ⁻¹ᵁ U)
    ((TensorTriplePullback.Construction.linePullbackUnit f (AbelianModuli.HilbertConstruction.Tensor.ProductSheaf.tensorModule (AbelianModuli.HilbertConstruction.Tensor.ProductSheaf.tensorModule (AbelianModuli.HilbertConstruction.Tensor.ProductSheaf.tensorModule M N) P) Q)).app U
      ((Picard.Homomorphisms.TensorAssociativity.Construction.tensorModuleBilinear (AbelianModuli.HilbertConstruction.Tensor.ProductSheaf.tensorModule (AbelianModuli.HilbertConstruction.Tensor.ProductSheaf.tensorModule M N) P) Q).app U
        ((Picard.Homomorphisms.TensorAssociativity.Construction.tensorModuleBilinear (AbelianModuli.HilbertConstruction.Tensor.ProductSheaf.tensorModule M N) P).app U ((Picard.Homomorphisms.TensorAssociativity.Construction.tensorModuleBilinear M N).app U m n) p) q)))
          (lineQuadrilinearPulledHom_fac f hM hN hP hQ b)
  change (lineQuadrilinearPulledHom f hM hN hP hQ b).app (f ⁻¹ᵁ U)
    ((TensorFourPullback.Construction.tensorFourPullbackMap f M N P Q).app (f ⁻¹ᵁ U) _) = _ at h
  rw [TensorFourPullback.Construction.tensorFourPullbackMap_app_unit, TensorTriplePullback.Construction.linePullbackUnit_natural, TensorQuadrilinear.Construction.lineQuadrilinearToHom_app_tensor] at h
  exact (TensorQuadrilinear.Construction.tensorQuadrilinearEquiv_apply _ _ _ _ _ _).trans h

end

end OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.QuadrilinearPullback.Construction

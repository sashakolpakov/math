import OAI.RepresentationTheory.Theta.Geometric.TwistFramesOnSubopens
import OAI.RepresentationTheory.Theta.Geometric.AlgebraicTensorFrames

/-! # Product Frames -/

namespace OAI.RepresentationTheory.Theta.Geometric.ProductFrames

noncomputable section

section

/-! Native local frames of the algebraic quotient of the consecutive
hyperplane pullbacks. -/

set_option backward.isDefEq.respectTransparency false
open _root_.CategoryTheory _root_.AlgebraicGeometry

variable {X : Scheme} {n m : ℕ} (f : X ⟶ AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.projectiveSpace n) (g : X ⟶ AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.projectiveSpace m)

def thetaQuotientOpen (i : Fin (n + 1)) (j : Fin (m + 1)) : X.Opens :=
  (f ⁻¹ᵁ AlgebraicGeometry.SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.coordinateOpen (R := ℂ) i) ⊓ (g ⁻¹ᵁ AlgebraicGeometry.SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.coordinateOpen (R := ℂ) j)

def thetaQuotientFrameOn (i : Fin (n + 1)) (j : Fin (m + 1)) (W : X.Opens)
    (hf : W ≤ f ⁻¹ᵁ AlgebraicGeometry.SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.coordinateOpen (R := ℂ) i)
    (hg : W ≤ g ⁻¹ᵁ AlgebraicGeometry.SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.coordinateOpen (R := ℂ) j) :
    (AlgebraicQuotient.algebraicThetaQuotient f g).sheaf.restrict W.ι ≅ AlgebraicGeometry.SheafCohomology.Projective.Invertible.Scheme.Modules.unitObj W.toScheme :=
  AlgebraicTensorFrames.algebraicTensorOpenFrame
    (AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullback g (AlgebraicQuotient.algebraicTwistBundle m 1)).sheaf
    (AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullback f (AlgebraicQuotient.algebraicTwistBundle n (-1))).sheaf W
    (TwistFramesOnSubopens.algebraicPullbackTwistFrameOn g 1 j W hg) (TwistFramesOnSubopens.algebraicPullbackTwistFrameOn f (-1) i W hf)

def thetaQuotientFrame (i : Fin (n + 1)) (j : Fin (m + 1)) :
    (AlgebraicQuotient.algebraicThetaQuotient f g).sheaf.restrict (thetaQuotientOpen f g i j).ι ≅
      AlgebraicGeometry.SheafCohomology.Projective.Invertible.Scheme.Modules.unitObj (thetaQuotientOpen f g i j).toScheme :=
  thetaQuotientFrameOn f g i j _ inf_le_left inf_le_right

theorem thetaQuotientFrameOn_restrict (i : Fin (n + 1)) (j : Fin (m + 1)) {U V : X.Opens}
    (h : V ≤ U) (hf : U ≤ f ⁻¹ᵁ AlgebraicGeometry.SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.coordinateOpen (R := ℂ) i)
    (hg : U ≤ g ⁻¹ᵁ AlgebraicGeometry.SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.coordinateOpen (R := ℂ) j) :
    AlgebraicGeometry.SheafCohomology.Projective.OpenFrames.Scheme.Modules.restrictOpenTrivialization h (thetaQuotientFrameOn f g i j U hf hg) =
      thetaQuotientFrameOn f g i j V (h.trans hf) (h.trans hg) := by
  unfold thetaQuotientFrameOn
  rw [AlgebraicTensorFrames.algebraicTensorOpenFrame_restrict, TwistFramesOnSubopens.algebraicPullbackTwistFrameOn_restrict,
    TwistFramesOnSubopens.algebraicPullbackTwistFrameOn_restrict]

theorem thetaQuotientFrameOn_transition (i k : Fin (n + 1)) (j l : Fin (m + 1)) (W : X.Opens)
    (hf : W ≤ f ⁻¹ᵁ AlgebraicGeometry.SheafCohomology.Projective.CoordinateExtensions.MvPolynomial.coordinateOpenOverlap (R := ℂ) i k)
    (hg : W ≤ g ⁻¹ᵁ AlgebraicGeometry.SheafCohomology.Projective.CoordinateExtensions.MvPolynomial.coordinateOpenOverlap (R := ℂ) j l) :
    (thetaQuotientFrameOn f g i j W
      (hf.trans (f.preimage_mono (AlgebraicGeometry.SheafCohomology.Projective.CoordinateExtensions.MvPolynomial.coordinateOpenOverlap_le_left (R := ℂ) i k)))
      (hg.trans (g.preimage_mono (AlgebraicGeometry.SheafCohomology.Projective.CoordinateExtensions.MvPolynomial.coordinateOpenOverlap_le_left (R := ℂ) j l)))).hom =
    (thetaQuotientFrameOn f g k l W
      (hf.trans (f.preimage_mono (AlgebraicGeometry.SheafCohomology.Projective.CoordinateExtensions.MvPolynomial.coordinateOpenOverlap_le_right (R := ℂ) i k)))
      (hg.trans (g.preimage_mono (AlgebraicGeometry.SheafCohomology.Projective.CoordinateExtensions.MvPolynomial.coordinateOpenOverlap_le_right (R := ℂ) j l)))).hom ≫
      AlgebraicGeometry.SheafCohomology.Projective.UnitScalar.unitEndomorphismOfTopSection (W.topIso.inv
        ((PowerGaugeCover.restrictRegularUnit hg (PowerGauge.projectivePullbackTransitionUnit g j l) *
          (PowerGaugeCover.restrictRegularUnit hf (PowerGauge.projectivePullbackTransitionUnit f i k))⁻¹ : Γ(X, W)ˣ) : Γ(X, W))) := by
  have h := AlgebraicTensorFrames.algebraicTensorOpenFrame_scalar
    (AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullback g (AlgebraicQuotient.algebraicTwistBundle m 1)).sheaf
    (AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullback f (AlgebraicQuotient.algebraicTwistBundle n (-1))).sheaf W _ _ _ _ _ _
    (TwistFramesOnSubopens.algebraicPullbackTwistFrameOn_transition g 1 j l W hg)
    (TwistFramesOnSubopens.algebraicPullbackTwistFrameOn_transition f (-1) i k W hf)
  apply h.trans
  congr 2
  rw [← map_mul, zpow_one, zpow_neg_one]
  rfl

end

/-! Native frames of finite products of hyperplane pullbacks. The frames
restrict compatibly and their transition unit is the product of the
original projective transition units. -/

set_option backward.isDefEq.respectTransparency false
open _root_.CategoryTheory _root_.AlgebraicGeometry

variable {X : Scheme} {n : ℕ}

def thetaProductModule : {r : ℕ} → (Fin (r + 1) → (X ⟶ AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.projectiveSpace n)) → X.Modules
  | 0, f => (AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullback (f 0) (AlgebraicQuotient.algebraicTwistBundle n 1)).sheaf
  | r + 1, f => AlgebraicGeometry.AbelianModuli.HilbertConstruction.Tensor.ProductSheaf.tensorModule (thetaProductModule (fun k : Fin (r + 1) => f k.castSucc))
      (AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullback (f (Fin.last (r + 1))) (AlgebraicQuotient.algebraicTwistBundle n 1)).sheaf

def thetaProductFrameOn : {r : ℕ} → (f : Fin (r + 1) → (X ⟶ AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.projectiveSpace n)) →
    (i : Fin (r + 1) → Fin (n + 1)) → (W : X.Opens) →
    (∀ k, W ≤ f k ⁻¹ᵁ AlgebraicGeometry.SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.coordinateOpen (R := ℂ) (i k)) →
    ((ProductFrames.thetaProductModule f).restrict W.ι ≅ AlgebraicGeometry.SheafCohomology.Projective.Invertible.Scheme.Modules.unitObj W.toScheme)
  | 0, f, i, W, hW => TwistFramesOnSubopens.algebraicPullbackTwistFrameOn (f 0) 1 (i 0) W (hW 0)
  | r + 1, f, i, W, hW => AlgebraicTensorFrames.algebraicTensorOpenFrame _ _ W
      (thetaProductFrameOn (fun k : Fin (r + 1) => f k.castSucc)
        (fun k => i k.castSucc) W (fun k => hW k.castSucc))
      (TwistFramesOnSubopens.algebraicPullbackTwistFrameOn (f (Fin.last (r + 1))) 1 (i (Fin.last (r + 1))) W
        (hW (Fin.last (r + 1))))

theorem thetaProductFrameOn_restrict {r : ℕ} (f : Fin (r + 1) → (X ⟶ AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.projectiveSpace n))
    (i : Fin (r + 1) → Fin (n + 1)) {U V : X.Opens} (h : V ≤ U)
    (hU : ∀ k, U ≤ f k ⁻¹ᵁ AlgebraicGeometry.SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.coordinateOpen (R := ℂ) (i k)) :
    AlgebraicGeometry.SheafCohomology.Projective.OpenFrames.Scheme.Modules.restrictOpenTrivialization h (ProductFrames.thetaProductFrameOn f i U hU) =
      ProductFrames.thetaProductFrameOn f i V (fun k => h.trans (hU k)) := by
  induction r with
  | zero => exact TwistFramesOnSubopens.algebraicPullbackTwistFrameOn_restrict (f 0) 1 (i 0) h (hU 0)
  | succ r ih =>
      simp only [ProductFrames.thetaProductFrameOn, AlgebraicTensorFrames.algebraicTensorOpenFrame_restrict,
        TwistFramesOnSubopens.algebraicPullbackTwistFrameOn_restrict, ih]

def thetaProductTransitionUnit {r : ℕ} (f : Fin (r + 1) → (X ⟶ AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.projectiveSpace n))
    (i j : Fin (r + 1) → Fin (n + 1)) (W : X.Opens)
    (hW : ∀ k, W ≤ f k ⁻¹ᵁ AlgebraicGeometry.SheafCohomology.Projective.CoordinateExtensions.MvPolynomial.coordinateOpenOverlap (R := ℂ) (i k) (j k)) :
    Γ(X, W)ˣ :=
  ∏ k, PowerGaugeCover.restrictRegularUnit (hW k) (PowerGauge.projectivePullbackTransitionUnit (f k) (i k) (j k))

theorem thetaProductFrameOn_transition {r : ℕ} (f : Fin (r + 1) → (X ⟶ AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.projectiveSpace n))
    (i j : Fin (r + 1) → Fin (n + 1)) (W : X.Opens)
    (hW : ∀ k, W ≤ f k ⁻¹ᵁ AlgebraicGeometry.SheafCohomology.Projective.CoordinateExtensions.MvPolynomial.coordinateOpenOverlap (R := ℂ) (i k) (j k)) :
    (ProductFrames.thetaProductFrameOn f i W (fun k => (hW k).trans
      ((f k).preimage_mono (AlgebraicGeometry.SheafCohomology.Projective.CoordinateExtensions.MvPolynomial.coordinateOpenOverlap_le_left (R := ℂ) (i k) (j k))))).hom =
    (ProductFrames.thetaProductFrameOn f j W (fun k => (hW k).trans
      ((f k).preimage_mono (AlgebraicGeometry.SheafCohomology.Projective.CoordinateExtensions.MvPolynomial.coordinateOpenOverlap_le_right (R := ℂ) (i k) (j k))))).hom ≫
      AlgebraicGeometry.SheafCohomology.Projective.UnitScalar.unitEndomorphismOfTopSection (W.topIso.inv (thetaProductTransitionUnit f i j W hW : Γ(X, W))) := by
  induction r with
  | zero =>
      have H := TwistFramesOnSubopens.algebraicPullbackTwistFrameOn_transition (f 0) 1 (i 0) (j 0) W (hW 0)
      apply H.trans
      congr 2
      rw [zpow_one, thetaProductTransitionUnit, Fin.prod_univ_one]
  | succ r ih =>
      have H := AlgebraicTensorFrames.algebraicTensorOpenFrame_scalar _ _ W _ _ _ _ _ _
        (ih (fun k : Fin (r + 1) => f k.castSucc) (fun k => i k.castSucc)
          (fun k => j k.castSucc) (fun k => hW k.castSucc))
        (TwistFramesOnSubopens.algebraicPullbackTwistFrameOn_transition (f (Fin.last (r + 1))) 1
          (i (Fin.last (r + 1))) (j (Fin.last (r + 1))) W (hW (Fin.last (r + 1))))
      apply H.trans
      congr 2
      rw [← map_mul, zpow_one]
      simp only [thetaProductTransitionUnit, Fin.prod_univ_castSucc, Units.val_mul, Units.coe_prod]

end

end OAI.RepresentationTheory.Theta.Geometric.ProductFrames

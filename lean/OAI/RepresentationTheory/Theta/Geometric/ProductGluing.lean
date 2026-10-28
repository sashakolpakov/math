import OAI.RepresentationTheory.Theta.Geometric.ProductFrames
import OAI.RepresentationTheory.Theta.Geometric.IntrinsicFrame.UnitGluing

/-! # Product Gluing -/

namespace OAI.RepresentationTheory.Theta.Geometric.ProductGluing

noncomputable section

/-! Gluing native tensor products of hyperplane pullbacks from regular
comparison units and their product transition law. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

theorem thetaProduct_iso_of_comparison_gauges {X : Scheme} {n r s : ℕ}
    (f₀ : Fin (r + 1) → (X ⟶ AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.projectiveSpace n))
    (f₁ : Fin (s + 1) → (X ⟶ AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.projectiveSpace n))
    (U : (Fin (r + 1) → Fin (n + 1)) × (Fin (s + 1) → Fin (n + 1)) → X.Opens)
    (hU : iSup U = ⊤)
    (hU₀ : ∀ p k, U p ≤ f₀ k ⁻¹ᵁ AlgebraicGeometry.SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.coordinateOpen (R := ℂ) (p.1 k))
    (hU₁ : ∀ p k, U p ≤ f₁ k ⁻¹ᵁ AlgebraicGeometry.SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.coordinateOpen (R := ℂ) (p.2 k))
    (v : ∀ p, Γ(X, U p)ˣ)
    (hW₀ : ∀ p q k, U p ⊓ U q ≤
      f₀ k ⁻¹ᵁ AlgebraicGeometry.SheafCohomology.Projective.CoordinateExtensions.MvPolynomial.coordinateOpenOverlap (R := ℂ) (p.1 k) (q.1 k))
    (hW₁ : ∀ p q k, U p ⊓ U q ≤
      f₁ k ⁻¹ᵁ AlgebraicGeometry.SheafCohomology.Projective.CoordinateExtensions.MvPolynomial.coordinateOpenOverlap (R := ℂ) (p.2 k) (q.2 k))
    (hv : ∀ p q,
      PowerGaugeCover.restrictRegularUnit (show U p ⊓ U q ≤ U q from inf_le_right) (v q) *
        ProductFrames.thetaProductTransitionUnit f₀ p.1 q.1 (U p ⊓ U q) (hW₀ p q) =
      PowerGaugeCover.restrictRegularUnit (show U p ⊓ U q ≤ U p from inf_le_left) (v p) *
        ProductFrames.thetaProductTransitionUnit f₁ p.2 q.2 (U p ⊓ U q) (hW₁ p q)) :
    Nonempty (ProductFrames.thetaProductModule f₁ ≅ ProductFrames.thetaProductModule f₀) := by
  apply IntrinsicFrame.UnitGluing.exists_iso_of_open_framed_units _ _ U hU
    (fun p => ProductFrames.thetaProductFrameOn f₁ p.2 (U p) (hU₁ p))
    (fun p => ProductFrames.thetaProductFrameOn f₀ p.1 (U p) (hU₀ p)) v
    (fun p q => (ProductFrames.thetaProductTransitionUnit f₁ p.2 q.2 (U p ⊓ U q) (hW₁ p q) : Γ(X, U p ⊓ U q)))
    (fun p q => (ProductFrames.thetaProductTransitionUnit f₀ p.1 q.1 (U p ⊓ U q) (hW₀ p q) : Γ(X, U p ⊓ U q)))
  · intro p q
    rw [ProductFrames.thetaProductFrameOn_restrict, ProductFrames.thetaProductFrameOn_restrict]
    exact ProductFrames.thetaProductFrameOn_transition f₁ p.2 q.2 (U p ⊓ U q) (hW₁ p q)
  · intro p q
    rw [ProductFrames.thetaProductFrameOn_restrict, ProductFrames.thetaProductFrameOn_restrict]
    exact ProductFrames.thetaProductFrameOn_transition f₀ p.1 q.1 (U p ⊓ U q) (hW₀ p q)
  · intro p q
    exact (mul_comm _ _).trans (congrArg Units.val (hv p q).symm)

end

end OAI.RepresentationTheory.Theta.Geometric.ProductGluing

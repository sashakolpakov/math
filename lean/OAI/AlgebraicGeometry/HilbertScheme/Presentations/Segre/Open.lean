import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Has

/-! # Open -/

namespace OAI.AlgebraicGeometry.HilbertScheme.Presentations

noncomputable section

/-! The O(1,1) polarization is specified by the Segre coordinate equations on
all standard affine charts. These equalities are equalities of sections, so
they also retain the scheme structure over nonreduced bases. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry _root_.MvPolynomial

universe u

variable {S : Scheme.{u}} {X Y : Over S}

def Has.Core.ProjectivePresentation.coefficientEmbedding (B : Has.Core.ProjectivePresentation X) :
    X.left ⟶ Proj (Hilbert.Polynomial.GradedHilbert.grading Γ(S, ⊤) B.dimension) := B.embedding ≫ pullback.fst _ _

def Has.Core.ProjectivePresentation.coordinateOpen (B : Has.Core.ProjectivePresentation X)
    (i : Fin (B.dimension + 1)) : X.left.Opens :=
  B.coefficientEmbedding ⁻¹ᵁ Proj.basicOpen (Hilbert.Polynomial.GradedHilbert.grading Γ(S, ⊤) B.dimension) (MvPolynomial.X i)

def Has.Core.ProjectivePresentation.coordinateRatio (B : Has.Core.ProjectivePresentation X)
    (i j : Fin (B.dimension + 1)) : Γ(X.left, B.coordinateOpen i) :=
  B.coefficientEmbedding.app _
    (Proj.awayToSection (Hilbert.Polynomial.GradedHilbert.grading Γ(S, ⊤) B.dimension) (MvPolynomial.X i)
      (Dehomogenization.GradedHilbert.dehomogenize i (MvPolynomial.X j)))

/-- The Segre embedding is characterized by its chart domains and the formula
z_(a,b)/z_(i,j) = (x_a/x_i)(y_b/y_j). In particular the selected very ample
bundle on the product is precisely O(1,1). -/
def Segre.Open.Core.IsSegrePresentation (BX : Has.Core.ProjectivePresentation X) (BY : Has.Core.ProjectivePresentation Y)
    (B : Has.Core.ProjectivePresentation (X ⨯ Y)) : Prop :=
  ∃ c : Fin (B.dimension + 1) ≃ Fin (BX.dimension + 1) × Fin (BY.dimension + 1),
    ∀ (i : Fin (BX.dimension + 1)) (j : Fin (BY.dimension + 1)),
      let U := (prod.fst : X ⨯ Y ⟶ X).left ⁻¹ᵁ BX.coordinateOpen i ⊓
        (prod.snd : X ⨯ Y ⟶ Y).left ⁻¹ᵁ BY.coordinateOpen j
      ∃ h : U = B.coordinateOpen (c.symm (i, j)),
        ∀ (a : Fin (BX.dimension + 1)) (b : Fin (BY.dimension + 1)),
          (X ⨯ Y).left.presheaf.map (homOfLE h.le).op
              (B.coordinateRatio (c.symm (i, j)) (c.symm (a, b))) =
            (prod.fst : X ⨯ Y ⟶ X).left.appLE _ U inf_le_left (BX.coordinateRatio i a) *
            (prod.snd : X ⨯ Y ⟶ Y).left.appLE _ U inf_le_right (BY.coordinateRatio j b)

end

end OAI.AlgebraicGeometry.HilbertScheme.Presentations

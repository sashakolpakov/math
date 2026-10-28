import OAI.AlgebraicGeometry.HilbertScheme.Presentations.MatrixPivot.Cokernel
import OAI.AlgebraicGeometry.HilbertScheme.Presentations.SectionUnitZeroLocus

/-! # Locus -/

namespace OAI.AlgebraicGeometry.HilbertScheme.Presentations.MatrixPivot.Locus.Grassmannian

noncomputable section

/-! Actual relative schemes for finite-presentation pivot charts, with verified free cokernels over every test scheme. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

variable {ι κ τ : Type u} [Fintype ι] [Fintype κ] [Fintype τ]
variable [DecidableEq ι] [DecidableEq κ] [DecidableEq τ]

def matrixPivotCondition {R T : Type u} [CommRing R] [CommRing T]
    (A : Matrix ι ι R) (B : Matrix ι κ R) (C : Matrix τ ι R) (D : Matrix τ κ R)
    (φ : R →+* T) : Prop :=
  IsUnit (φ A.det) ∧ ∀ p : τ × κ, φ (Cokernel.Grassmannian.pivotResidual A B C D p.1 p.2) = 0

def matrixPivotConditionCokernelEquiv {R T : Type u} [CommRing R] [CommRing T]
    (A : Matrix ι ι R) (B : Matrix ι κ R) (C : Matrix τ ι R) (D : Matrix τ κ R)
    (φ : R →+* T) (h : matrixPivotCondition A B C D φ) :
    (((ι → T) × (τ → T)) ⧸
      (Grassmannian.Incidence.blockLinearMap (Matrix.toLin' (A.map φ)) (Matrix.toLin' (B.map φ))
        (Matrix.toLin' (C.map φ)) (Matrix.toLin' (D.map φ))).range) ≃ₗ[T] (τ → T) := by
  apply Cokernel.Grassmannian.matrixPivotCokernelEquiv
  · have hd : φ A.det = (A.map φ).det := φ.map_det A
    exact hd ▸ h.1
  · rw [← Cokernel.Grassmannian.pivotResidual_map φ]
    ext i j
    exact h.2 (i, j)

variable {S : Scheme.{u}} (M : Over S)
variable (A : Matrix ι ι Γ(M.left, ⊤)) (B : Matrix ι κ Γ(M.left, ⊤))
variable (C : Matrix τ ι Γ(M.left, ⊤)) (D : Matrix τ κ Γ(M.left, ⊤))

def matrixPivotSubfunctor : Subfunctor (yoneda.obj M) :=
  SectionUnitZeroLocus.sectionUnitZeroSubfunctor M A.det (fun p : τ × κ => Cokernel.Grassmannian.pivotResidual A B C D p.1 p.2)

omit [Fintype κ] [Fintype τ] [DecidableEq κ] [DecidableEq τ] in
theorem matrix_pivot_locus_representable :
    ∃ (U : Over S) (j : U ⟶ M), IsOpenImmersion j.left ∧
      ∃ (Z : Over S) (k : Z ⟶ U), IsClosedImmersion k.left ∧
        ∃ e : yoneda.obj Z ≅ (matrixPivotSubfunctor M A B C D).toFunctor,
          e.hom ≫ (matrixPivotSubfunctor M A B C D).ι = yoneda.map (k ≫ j) :=
  SectionUnitZeroLocus.section_unit_zero_locus_representable M A.det (fun p : τ × κ => Cokernel.Grassmannian.pivotResidual A B C D p.1 p.2)

def matrixPivotPointCokernelEquiv {T : Over S}
    (x : (matrixPivotSubfunctor M A B C D).toFunctor.obj (Opposite.op T)) :
    (((ι → Γ(T.left, ⊤)) × (τ → Γ(T.left, ⊤))) ⧸
      (Grassmannian.Incidence.blockLinearMap (Matrix.toLin' (A.map x.val.left.appTop.hom))
        (Matrix.toLin' (B.map x.val.left.appTop.hom)) (Matrix.toLin' (C.map x.val.left.appTop.hom))
        (Matrix.toLin' (D.map x.val.left.appTop.hom))).range) ≃ₗ[Γ(T.left, ⊤)] (τ → Γ(T.left, ⊤)) :=
  matrixPivotConditionCokernelEquiv A B C D x.val.left.appTop.hom x.property

end

end OAI.AlgebraicGeometry.HilbertScheme.Presentations.MatrixPivot.Locus.Grassmannian

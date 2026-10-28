import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Normalized.Chart

/-! # Overlap Functor -/

namespace OAI.AlgebraicGeometry.HilbertScheme.Presentations.Normalized.OverlapFunctor.Grassmannian

noncomputable section

/-! Natural coordinate changes on the determinant-open overlap functors. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

variable {ι ν : Type u} [Fintype ι] [DecidableEq ι]
variable (a b : ι → ν) (S : Scheme.{u})

def normalizedOverlapSubfunctor : Subfunctor (Grassmannian.Chart.matrixFunctor ι ν S) where
  obj _T := {Q | Matrices.Grassmannian.IsNormalized a Q ∧ IsUnit (Matrices.Grassmannian.selectedColumns b Q).det}
  map f Q hQ := by
    refine ⟨hQ.1.map f.unop.left.appTop.hom, ?_⟩
    exact ((congrArg IsUnit (f.unop.left.appTop.hom.map_det
      (Matrices.Grassmannian.selectedColumns b Q))).mp (hQ.2.map f.unop.left.appTop.hom))

def normalizedOverlapForget :
    (normalizedOverlapSubfunctor a b S).toFunctor ⟶
      (Chart.Grassmannian.normalizedMatrixSubfunctor a S).toFunctor where
  app _T := ↾fun Q => ⟨Q.val, Q.property.1⟩
  naturality := by intros; rfl

def normalizedOverlapPointEquiv (T : Over S) :
    (normalizedOverlapSubfunctor a b S).obj (.op T) ≃
      (normalizedOverlapSubfunctor b a S).obj (.op T) where
  toFun Q := ⟨Matrices.Grassmannian.normalizeColumns b Q.val, Matrices.Grassmannian.normalizeColumns_normalized b Q.val Q.property.2, by
    apply (Matrices.Grassmannian.normalizeColumns_pivot_isUnit_iff a b Q.val Q.property.2).mpr
    rw [Q.property.1, Matrix.det_one]
    exact isUnit_one⟩
  invFun Q := ⟨Matrices.Grassmannian.normalizeColumns a Q.val, Matrices.Grassmannian.normalizeColumns_normalized a Q.val Q.property.2, by
    apply (Matrices.Grassmannian.normalizeColumns_pivot_isUnit_iff b a Q.val Q.property.2).mpr
    rw [Q.property.1, Matrix.det_one]
    exact isUnit_one⟩
  left_inv Q := Subtype.ext (Matrices.Grassmannian.normalizeColumns_inverse a b Q.val Q.property.1 Q.property.2)
  right_inv Q := Subtype.ext (Matrices.Grassmannian.normalizeColumns_inverse b a Q.val Q.property.1 Q.property.2)

def normalizedOverlapSwap :
    (normalizedOverlapSubfunctor a b S).toFunctor ≅
      (normalizedOverlapSubfunctor b a S).toFunctor :=
  NatIso.ofComponents (fun T => (normalizedOverlapPointEquiv a b S T.unop).toIso) (by
    intro T U f
    apply ConcreteCategory.hom_ext
    intro Q
    apply Subtype.ext
    exact Matrices.Grassmannian.normalizeColumns_map f.unop.left.appTop.hom b Q.val Q.property.2)

theorem normalizedOverlapSwap_self : normalizedOverlapSwap a a S = Iso.refl _ := by
  apply Iso.ext
  apply NatTrans.ext
  funext T
  apply ConcreteCategory.hom_ext
  intro Q
  apply Subtype.ext
  exact Matrices.Grassmannian.normalizeColumns_of_normalized a Q.val Q.property.1

end

end OAI.AlgebraicGeometry.HilbertScheme.Presentations.Normalized.OverlapFunctor.Grassmannian

import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Grassmannian.CoordinateCharts
import Mathlib.AlgebraicGeometry.AffineSpace
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.CategoryTheory.NatIso

/-! # Chart -/

namespace OAI.AlgebraicGeometry.HilbertScheme.Presentations.Grassmannian.Chart

noncomputable section

/-!
Affine schemes representing the standard Grassmannian charts. Chart objects
are the submodules and quotient-isomorphism condition from Grassmannian;
restriction acts by applying the ring map to their matrix coordinates.
-/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
open scoped _root_.AlgebraicGeometry

universe u

variable (ι κ : Type u) [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]

def matrixChartEquiv (R : Type u) [CommRing R] :
    Matrix ι κ R ≃ CoordinateCharts.Chart R (ι → R) (κ → R) :=
  Matrix.toLin'.toEquiv.trans CoordinateCharts.chartEquiv

variable (S : Scheme.{u})

def matrixFunctor : (Over S)ᵒᵖ ⥤ Type u where
  obj T := Matrix ι κ Γ(T.unop.left, ⊤)
  map a := ↾fun M i j => a.unop.left.appTop (M i j)
  map_id _T := rfl
  map_comp _a _b := rfl

def chartFunctor : (Over S)ᵒᵖ ⥤ Type u :=
  (matrixFunctor ι κ S).copyObj
    (fun T => CoordinateCharts.Chart Γ(T.unop.left, ⊤)
      (ι → Γ(T.unop.left, ⊤)) (κ → Γ(T.unop.left, ⊤)))
    (fun T => (matrixChartEquiv ι κ Γ(T.unop.left, ⊤)).toIso)

def matrixSpace : Over S :=
  Over.mk (AffineSpace (ι × κ) S ↘ S)

/-- Affine-space points are precisely the matrices of quotient coordinates. -/
def matrixPointEquiv (T : Over S) :
    (T ⟶ matrixSpace ι κ S) ≃ Matrix ι κ Γ(T.left, ⊤) where
  toFun f i j := f.left.appTop (AffineSpace.coord S (i, j))
  invFun M := Over.homMk
    (AffineSpace.homOfVector T.hom (fun ij : ι × κ => M ij.1 ij.2))
    (AffineSpace.homOfVector_over _ _)
  left_inv f := by
    apply (Over.forget S).map_injective
    apply AffineSpace.hom_ext
    · exact (AffineSpace.homOfVector_over _ _).trans f.w.symm
    · intro ij
      exact AffineSpace.homOfVector_appTop_coord _ _ ij
  right_inv M := by
    funext i j
    exact AffineSpace.homOfVector_appTop_coord _ _ (i, j)

/-- The representing equivalence is natural in arbitrary S-schemes. -/
def matrixRepresentation :
    yoneda.obj (matrixSpace ι κ S) ≅ matrixFunctor ι κ S :=
  NatIso.ofComponents (fun T => (matrixPointEquiv ι κ S T.unop).toIso) (by
    intro T U a
    apply ConcreteCategory.hom_ext
    intro f
    funext i j
    rfl)

/-- A standard Grassmannian chart is represented by affine space over S. -/
def chartRepresentation :
    yoneda.obj (matrixSpace ι κ S) ≅ chartFunctor ι κ S :=
  matrixRepresentation ι κ S ≪≫
    (matrixFunctor ι κ S).isoCopyObj _ _

omit [Fintype ι] [DecidableEq ι] in
theorem chartFunctor_map_coordinates {T U : (Over S)ᵒᵖ} (a : T ⟶ U)
    (N : (chartFunctor ι κ S).obj T) (i : ι) (j : κ) :
    (matrixChartEquiv ι κ Γ(U.unop.left, ⊤)).symm
        ((chartFunctor ι κ S).map a N) i j =
      a.unop.left.appTop
        ((matrixChartEquiv ι κ Γ(T.unop.left, ⊤)).symm N i j) := by
  change (matrixChartEquiv ι κ Γ(U.unop.left, ⊤)).symm
      ((matrixChartEquiv ι κ Γ(U.unop.left, ⊤))
        (fun i j => a.unop.left.appTop
          ((matrixChartEquiv ι κ Γ(T.unop.left, ⊤)).symm N i j))) i j = _
  exact congrArg (fun M : Matrix ι κ Γ(U.unop.left, ⊤) => M i j)
    ((matrixChartEquiv ι κ Γ(U.unop.left, ⊤)).symm_apply_apply _)

end

end OAI.AlgebraicGeometry.HilbertScheme.Presentations.Grassmannian.Chart

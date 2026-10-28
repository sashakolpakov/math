import Mathlib.Algebra.Homology.Additive
import Mathlib.CategoryTheory.Adjunction.Basic

/-! # Cochain Adjunction Transpose -/

namespace OAI.AlgebraicGeometry.Quotients.FiniteDescent.CochainAdjunctionTranspose.Construction.CochainAdjunction

noncomputable section

/-! Transposing a cochain map through an adjunction, component by component. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits

universe u v w z

variable {V : Type u} [Category.{v} V] [HasZeroMorphisms V]
variable {W : Type w} [Category.{z} W] [HasZeroMorphisms W]
variable {L : V ⥤ W} {R : W ⥤ V} [L.PreservesZeroMorphisms] [R.PreservesZeroMorphisms]
variable (a : L ⊣ R)
variable {C : CochainComplex V ℕ} {D : CochainComplex W ℕ}

def transpose (f : C ⟶ (R.mapHomologicalComplex (ComplexShape.up ℕ)).obj D) :
    (L.mapHomologicalComplex (ComplexShape.up ℕ)).obj C ⟶ D :=
  CochainComplex.ofHom (fun i => (a.homEquiv _ _).symm (f.f i)) (by
    intro i
    apply (a.homEquiv _ _).injective
    change a.homEquiv _ _ ((a.homEquiv _ _).symm (f.f i) ≫ D.d i (i + 1)) =
      a.homEquiv _ _ (L.map (C.d i (i + 1)) ≫ (a.homEquiv _ _).symm (f.f (i + 1)))
    rw [a.homEquiv_naturality_right, a.homEquiv_naturality_left]
    have hi := (a.homEquiv (C.X i) (D.X i)).apply_symm_apply (f.f i)
    have hj := (a.homEquiv (C.X (i + 1)) (D.X (i + 1))).apply_symm_apply (f.f (i + 1))
    exact (congrArg (fun z => z ≫ R.map (D.d i (i + 1))) hi).trans
      ((f.comm i (i + 1)).trans (congrArg (fun z => C.d i (i + 1) ≫ z) hj.symm)))

theorem transpose_component
    (f : C ⟶ (R.mapHomologicalComplex (ComplexShape.up ℕ)).obj D) (i : ℕ) :
    a.homEquiv _ _ ((transpose a f).f i) = f.f i :=
  (a.homEquiv _ _).apply_symm_apply _

end

end OAI.AlgebraicGeometry.Quotients.FiniteDescent.CochainAdjunctionTranspose.Construction.CochainAdjunction

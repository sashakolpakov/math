import OAI.AlgebraicGeometry.Picard.PoincareBundle.Kernel.Scheme
import Mathlib.AlgebraicGeometry.Morphisms.FlatRank

/-! # Degree -/

namespace OAI.AlgebraicGeometry.Picard.PoincareBundle.Kernel.Degree

noncomputable section

/-! Isomorphism of the full finite kernel schemes preserves the finite-flat degree, including infinitesimal length. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj

universe u

open OAI.AlgebraicGeometry.Picard.PoincareBundle.Kernel.Scheme

variable {S : Scheme.{u}} {A B D E : Over S} [GrpObj D] [GrpObj E]
  (f : A ⟶ D) (g : B ⟶ E) [IsFinite f.left] [Flat f.left] [IsFinite g.left] [Flat g.left]

/-- The actual kernel length is the finite-flat rank at the identity section. -/
theorem kernel_rank (s : S) : (Kernel.Scheme.kernelObject f).hom.finrank s = f.left.finrank (η[D].left s) := by
  rw [Kernel.Scheme.kernel_hom_eq_snd]
  exact Scheme.Hom.finrank_of_isPullback _ _ _ _ (Kernel.Scheme.kernel_isPullback f) s

/-- An isomorphism of the full kernel schemes preserves rank at the two identity sections. -/
theorem identity_degree_eq (e : Kernel.Scheme.kernelObject f ≅ Kernel.Scheme.kernelObject g) (s : S) :
    f.left.finrank (η[D].left s) = g.left.finrank (η[E].left s) := by
  have : IsFinite (Kernel.Scheme.kernelObject g).hom := Kernel.Scheme.kernel_isFinite g
  have : Flat (Kernel.Scheme.kernelObject g).hom := Kernel.Scheme.kernel_flat g
  have : IsIso e.hom.left := inferInstanceAs (IsIso ((Over.forget S).map e.hom))
  calc
    f.left.finrank (η[D].left s) = (Kernel.Scheme.kernelObject f).hom.finrank s := (kernel_rank f s).symm
    _ = (Kernel.Scheme.kernelObject g).hom.finrank s := by rw [← e.hom.w, Scheme.Hom.finrank_comp_left_of_isIso]
    _ = g.left.finrank (η[E].left s) := kernel_rank g s

/-- On connected targets, the full kernel isomorphism preserves degree at every target point. -/
theorem degree_eq [PreconnectedSpace D.left] [PreconnectedSpace E.left]
    [LocallyOfFinitePresentation f.left] [LocallyOfFinitePresentation g.left]
    (e : Kernel.Scheme.kernelObject f ≅ Kernel.Scheme.kernelObject g) (s : S) (a : D.left) (b : E.left) :
    f.left.finrank a = g.left.finrank b :=
  (f.left.isLocallyConstant_finrank.apply_eq_of_preconnectedSpace a (η[D].left s)).trans
    ((identity_degree_eq f g e s).trans
      (g.left.isLocallyConstant_finrank.apply_eq_of_preconnectedSpace (η[E].left s) b))

end

end OAI.AlgebraicGeometry.Picard.PoincareBundle.Kernel.Degree

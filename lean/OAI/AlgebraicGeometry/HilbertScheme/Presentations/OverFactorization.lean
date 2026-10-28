import OAI.AlgebraicGeometry.HilbertScheme.Presentations.SubfunctorRepresentations

/-! # Over Factorization -/

namespace OAI.AlgebraicGeometry.HilbertScheme.Presentations.OverFactorization

noncomputable section

/-! A factorization of the underlying scheme map automatically preserves
the fixed base scheme. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u
variable {S : Scheme.{u}} {T Y M : Over S}

def overHomOfFactorization (f : T.left ⟶ Y.left) (j : Y ⟶ M) (x : T ⟶ M)
    (h : f ≫ j.left = x.left) : T ⟶ Y :=
  Over.homMk f (by rw [← j.w, ← Category.assoc, h, x.w])

theorem overHomOfFactorization_comp (f : T.left ⟶ Y.left) (j : Y ⟶ M) (x : T ⟶ M)
    (h : f ≫ j.left = x.left) : overHomOfFactorization f j x h ≫ j = x :=
  Over.OverMorphism.ext h

end

end OAI.AlgebraicGeometry.HilbertScheme.Presentations.OverFactorization

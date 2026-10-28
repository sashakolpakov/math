import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Tor.ExactSequence
import Mathlib.Algebra.Homology.Linear
import Mathlib.Algebra.Homology.ShortComplex.Linear
import Mathlib.CategoryTheory.Monoidal.Linear

/-! # Linear -/

namespace OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Tor.Linear

noncomputable section

/-! The actual homology and native Tor functors are linear over the
coefficient ring, including the first argument of Tor. -/

open _root_.CategoryTheory _root_.CategoryTheory.MonoidalCategory

universe u v w

section Homology

variable (R : Type u) [Semiring R] (C : Type v) [Category.{w} C] [Abelian C]
  [CategoryTheory.Linear R C] {ι : Type*} (c : ComplexShape ι)

instance shortComplexFunctor_linear (i : ι) :
    Functor.Linear R (HomologicalComplex.shortComplexFunctor C c i) where
  map_smul := by intros; rfl

instance homologyFunctor_linear (i : ι) :
    Functor.Linear R (HomologicalComplex.homologyFunctor C c i) :=
  Functor.linear_of_iso R (HomologicalComplex.homologyFunctorIso C c i).symm

end Homology

variable (R : Type u) [CommRing R]

instance tensorComplexFunctor_linear (K : ChainComplex (ModuleCat.{u} R) ℕ) :
    Functor.Linear R (ExactSequence.tensorComplexFunctor R K) where
  map_smul := by
    intro M N f r
    apply HomologicalComplex.Hom.ext
    funext i
    exact (tensorRight (K.X i)).map_smul r f

instance tor_first_linear (N : ModuleCat.{u} R) (n : ℕ) :
    Functor.Linear R ((Tor (ModuleCat R) n).flip.obj N) :=
  Functor.linear_of_iso R (ExactSequence.torIso R N (projectiveResolution N) n).symm

end

end OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Tor.Linear

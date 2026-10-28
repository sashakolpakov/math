import OAI.AlgebraicGeometry.CycleClass.Thom.TorAlgebra.DiagonalModule
import OAI.AlgebraicGeometry.CycleClass.Thom.TorAlgebra.ExternalTensorSquare
import Mathlib.CategoryTheory.Monoidal.Tor

/-! # Diagonal Comparison -/

namespace OAI.AlgebraicGeometry.CycleClass.Thom.TorAlgebra.DiagonalComparison.Tor

noncomputable section

/-! Reduction to the diagonal for native Tor. The algebra coefficient
is the actual iterated tensor module; the comparison is computed from
a projective resolution of the multiplication module and its image. -/

open _root_.CategoryTheory _root_.CategoryTheory.MonoidalCategory
open scoped TensorProduct

open OAI.AlgebraicGeometry.CycleClass.Thom.TorAlgebra.DiagonalModule OAI.AlgebraicGeometry.CycleClass.Thom.TorAlgebra.ExternalTensorSquare
  ExternalTensorProjectives

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u
variable (k R : Type u) [Field k] [CommRing R] [Algebra k R]
  (M N : ModuleCat.{u} R)

local instance : (ExternalTensorProjectives.externalTensor k R R N).Additive := by
  dsimp [ExternalTensorProjectives.externalTensor, TensorOverBaseProjectives.tensorRestriction]
  infer_instance

def tensorComplexIso (P : ProjectiveResolution (DiagonalModule.diagonalModule k R)) :
    ((ModuleCat.restrictScalars (algebraMap R (R ⊗[k] R))).mapHomologicalComplex
      (ComplexShape.down ℕ)).obj
        (((tensorLeft (ExternalTensorSquare.externalCoefficient k R R N M)).mapHomologicalComplex
          (ComplexShape.down ℕ)).obj P.complex) ≅
    ((tensorLeft M).mapHomologicalComplex (ComplexShape.down ℕ)).obj
      ((DiagonalModule.tensorResolution k R N P).complex) :=
  (Functor.mapHomologicalComplexCompIso (ExternalTensorSquare.externalTensorSquare k R R N M)
    (ComplexShape.down ℕ)).app P.complex

def torIso (n : ℕ) :
    (ModuleCat.restrictScalars (algebraMap R (R ⊗[k] R))).obj
      (((Tor (ModuleCat (R ⊗[k] R)) n).obj (ExternalTensorSquare.externalCoefficient k R R N M)).obj
        (DiagonalModule.diagonalModule k R)) ≅
    (((Tor (ModuleCat R) n).obj M).obj N) := by
  let G := ModuleCat.restrictScalars (algebraMap R (R ⊗[k] R))
  let P := projectiveResolution (DiagonalModule.diagonalModule k R)
  let Q := DiagonalModule.tensorResolution k R N P
  let K := ((tensorLeft (ExternalTensorSquare.externalCoefficient k R R N M)).mapHomologicalComplex
    (ComplexShape.down ℕ)).obj P.complex
  exact G.mapIso (P.isoLeftDerivedObj (tensorLeft (ExternalTensorSquare.externalCoefficient k R R N M)) n) ≪≫
    ((K.sc n).mapHomologyIso G).symm ≪≫
    (HomologicalComplex.homologyFunctor (ModuleCat R) (ComplexShape.down ℕ) n).mapIso
      (tensorComplexIso k R M N P) ≪≫
    (Q.isoLeftDerivedObj (tensorLeft M) n).symm ≪≫
    ((Tor (ModuleCat R) n).obj M).mapIso (DiagonalModule.diagonalTensorIso k R N)

end

end OAI.AlgebraicGeometry.CycleClass.Thom.TorAlgebra.DiagonalComparison.Tor

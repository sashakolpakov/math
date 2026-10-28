import OAI.AlgebraicGeometry.CycleClass.Thom.TorAlgebra.IndependentResolution
import OAI.AlgebraicGeometry.CycleClass.Thom.TorAlgebra.TensorCancel

/-! # Independent Change Of Rings -/

namespace OAI.AlgebraicGeometry.CycleClass.Thom.TorAlgebra.IndependentChangeOfRings.Tor

noncomputable section

/-! Native change of rings when the algebra and the second module
are Tor-independent. The isomorphism is computed from the original
projective resolution and actual tensor cancellation. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.CategoryTheory.MonoidalCategory

open OAI.AlgebraicGeometry.CycleClass.Thom.TorAlgebra.FlatExtension OAI.AlgebraicGeometry.CycleClass.Thom.TorAlgebra.TensorCancel

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u
variable (R S : Type u) [CommRing R] [CommRing S] [Algebra R S]
  (M : ModuleCat.{u} S) (N : ModuleCat.{u} R)

def tensorComplexIso (P : ProjectiveResolution N) :
    ((ModuleCat.restrictScalars (algebraMap R S)).mapHomologicalComplex (ComplexShape.down ℕ)).obj
      (((tensorLeft M).mapHomologicalComplex (ComplexShape.down ℕ)).obj
        (((FlatExtension.baseChange R S).mapHomologicalComplex (ComplexShape.down ℕ)).obj P.complex)) ≅
    ((tensorLeft ((ModuleCat.restrictScalars (algebraMap R S)).obj M)).mapHomologicalComplex
      (ComplexShape.down ℕ)).obj P.complex :=
  (Functor.mapHomologicalComplexCompIso (TensorCancel.tensorCancelIso R S M) (ComplexShape.down ℕ)).app P.complex

variable (hv : ∀ n, IsZero (((Tor (ModuleCat R) (n + 1)).obj (ModuleCat.of R S)).obj N))

def torIso (n : ℕ) :
    (ModuleCat.restrictScalars (algebraMap R S)).obj
      (((Tor (ModuleCat S) n).obj M).obj ((FlatExtension.baseChange R S).obj N)) ≅
    (((Tor (ModuleCat R) n).obj ((ModuleCat.restrictScalars (algebraMap R S)).obj M)).obj N) := by
  let G := ModuleCat.restrictScalars (algebraMap R S)
  let P := projectiveResolution N
  let Q := IndependentResolution.Tor.resolution R S N hv P
  let K := ((tensorLeft M).mapHomologicalComplex (ComplexShape.down ℕ)).obj Q.complex
  exact G.mapIso (Q.isoLeftDerivedObj (tensorLeft M) n) ≪≫
    ((K.sc n).mapHomologyIso G).symm ≪≫
    (HomologicalComplex.homologyFunctor (ModuleCat R) (ComplexShape.down ℕ) n).mapIso
      (tensorComplexIso R S M N P) ≪≫
    (P.isoLeftDerivedObj (tensorLeft (G.obj M)) n).symm

end

end OAI.AlgebraicGeometry.CycleClass.Thom.TorAlgebra.IndependentChangeOfRings.Tor

import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.BettiEndAdditivity
import OAI.NumberTheory.PadicHodge.GeometricComparison.HeckeScalar
import OAI.NumberTheory.PadicHodge.GeometricComparison.Integrality

/-! # Betti Group Action -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison

noncomputable section

/-! The actual rational Betti pullbacks form an opposite ring action of algebraic group endomorphisms. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj TensorProduct

theorem BettiGroupAction.schemeBettiPullback_id {R : Type} [Ring R] (X : Over AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase) (n : ℕ) :
    (AlgebraicGeometry.Betti.Scheme.schemeBettiMap (ModuleCat.of R R) n (𝟙 X)).hom = LinearMap.id :=
  congrArg ModuleCat.Hom.hom ((AlgebraicGeometry.Betti.Scheme.schemeBettiFunctor (ModuleCat.of R R) n).map_id (Opposite.op X))

theorem BettiGroupAction.schemeBettiPullback_comp {R : Type} [Ring R] {X Y Z : Over AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase}
    (f : X ⟶ Y) (g : Y ⟶ Z) (n : ℕ) :
    (AlgebraicGeometry.Betti.Scheme.schemeBettiMap (ModuleCat.of R R) n (f ≫ g)).hom =
      (AlgebraicGeometry.Betti.Scheme.schemeBettiMap (ModuleCat.of R R) n f).hom.comp (AlgebraicGeometry.Betti.Scheme.schemeBettiMap (ModuleCat.of R R) n g).hom :=
  congrArg ModuleCat.Hom.hom ((AlgebraicGeometry.Betti.Scheme.schemeBettiFunctor (ModuleCat.of R R) n).map_comp g.op f.op)

variable {K : Type} [Field K] [NumberField K]
  {q : ℕ} [Fact q.Prime] {jq : K →+* ℚ_[q]} (A : Geometry.AbelianH1Model K q jq)
  (j : K →+* ℂ)

def Geometry.AbelianH1Model.complexAbelianVariety
    (P : AlgebraicGeometry.Foundations.Scheme.SmoothProjective.ProjectivePresentation (A.complexFiber j).scheme.left (A.complexFiber j).scheme.hom) :
    AlgebraicGeometry.ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety := by
  letI : ConnectedSpace (A.complexFiber j).scheme.left :=
    GeometricallyConnected.connectedSpace_of_subsingleton (A.complexFiber j).scheme.hom
  have hIntegral : IsIntegral (A.complexFiber j).scheme.left :=
    Integrality.GeometricIntegrality.smooth_connected_integral (A.complexFiber j).scheme.hom
  exact { variety := ⟨A.smoothProjectiveFiber j P, hIntegral⟩
          group := (A.complexFiber j).group
          commutative := (A.complexFiber j).commutative }

def Geometry.AbelianH1Model.algebraicBettiPullback (f : AlgebraicGeometry.FormalGeometry.Completion.Endomorphisms.Construction.AlgebraicEnd A.variety.scheme) : Module.End ℚ (A.Betti j) :=
  (AlgebraicGeometry.Betti.Scheme.schemeBettiMap (ModuleCat.of ℚ ℚ) 1
    ((Over.pullback (Geometry.scalarBaseMap j)).map f.toMul.hom.hom)).hom

theorem Geometry.AbelianH1Model.algebraicBettiPullback_one : A.algebraicBettiPullback j 1 = 1 := by
  change (AlgebraicGeometry.Betti.Scheme.schemeBettiMap (ModuleCat.of ℚ ℚ) 1
    ((Over.pullback (Geometry.scalarBaseMap j)).map (𝟙 A.variety.scheme))).hom = _
  erw [(Over.pullback (Geometry.scalarBaseMap j)).map_id]
  exact BettiGroupAction.schemeBettiPullback_id _ 1

theorem Geometry.AbelianH1Model.algebraicBettiPullback_mul (f g : AlgebraicGeometry.FormalGeometry.Completion.Endomorphisms.Construction.AlgebraicEnd A.variety.scheme) :
    A.algebraicBettiPullback j (f * g) = A.algebraicBettiPullback j g * A.algebraicBettiPullback j f := by
  change (AlgebraicGeometry.Betti.Scheme.schemeBettiMap (ModuleCat.of ℚ ℚ) 1
    ((Over.pullback (Geometry.scalarBaseMap j)).map (g.toMul.hom.hom ≫ f.toMul.hom.hom))).hom = _
  rw [Functor.map_comp]
  exact BettiGroupAction.schemeBettiPullback_comp _ _ 1

variable (P : AlgebraicGeometry.Foundations.Scheme.SmoothProjective.ProjectivePresentation (A.complexFiber j).scheme.left (A.complexFiber j).scheme.hom)

include P in
theorem Geometry.AbelianH1Model.algebraicBettiPullback_add (f g : AlgebraicGeometry.FormalGeometry.Completion.Endomorphisms.Construction.AlgebraicEnd A.variety.scheme) :
    A.algebraicBettiPullback j (f + g) = A.algebraicBettiPullback j f + A.algebraicBettiPullback j g := by
  change (AlgebraicGeometry.Betti.Scheme.schemeBettiMap (ModuleCat.of ℚ ℚ) 1
    ((Over.pullback (Geometry.scalarBaseMap j)).map (f.toMul.hom.hom * g.toMul.hom.hom))).hom = _
  rw [Functor.map_mul]
  exact LinearMap.ext (AlgebraicGeometry.HodgeConjecture.HeckeCycles.BettiEndAdditivity.CM.rational_pullback_mul (A.complexAbelianVariety j P) _ _)

def Geometry.AbelianH1Model.algebraicBettiMonoidAction :
    (AlgebraicGeometry.FormalGeometry.Completion.Endomorphisms.Construction.AlgebraicEnd A.variety.scheme)ᵐᵒᵖ →* Module.End ℚ (A.Betti j) where
  toFun f := A.algebraicBettiPullback j f.unop
  map_one' := A.algebraicBettiPullback_one j
  map_mul' f g := A.algebraicBettiPullback_mul j g.unop f.unop

def Geometry.AbelianH1Model.algebraicBettiRingAction :
    (AlgebraicGeometry.FormalGeometry.Completion.Endomorphisms.Construction.AlgebraicEnd A.variety.scheme)ᵐᵒᵖ →+* Module.End ℚ (A.Betti j) :=
  RingHom.mk' (A.algebraicBettiMonoidAction j)
    (fun f g => A.algebraicBettiPullback_add j P f.unop g.unop)

end

end OAI.NumberTheory.PadicHodge.GeometricComparison

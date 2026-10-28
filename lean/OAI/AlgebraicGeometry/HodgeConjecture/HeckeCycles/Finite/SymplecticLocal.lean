import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Local.MatrixPivot
import OAI.RepresentationTheory.Theta.PoissonAutomorphyFiniteFourier

/-! # Symplectic Local -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Finite.SymplecticLocal.CM

noncomputable section

/-! Actual local and integral symplectic matrices obtained by evaluating
a finite-adelic symplectic matrix. Integrality holds at almost all places. -/

open scoped Classical RestrictedProduct _root_.Matrix
open Filter OAI.RepresentationTheory.Theta.PoissonAutomorphyFiniteFourier.Construction
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Local.MatrixPivot.CM.SymplecticBigCell

def localEval (v : RepresentationTheory.Theta.AdelicSupport.PoissonAutomorphyConstruction.FinitePlace) : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQf →+* v.adicCompletion ℚ :=
  RestrictedProduct.evalRingHom (fun w : RepresentationTheory.Theta.AdelicSupport.PoissonAutomorphyConstruction.FinitePlace => w.adicCompletion ℚ) v

variable {I : Type*} [Fintype I]

def localSymplectic (g : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.Sp I RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQf) (v : RepresentationTheory.Theta.AdelicSupport.PoissonAutomorphyConstruction.FinitePlace) : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.Sp I (v.adicCompletion ℚ) :=
  RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.mapSp (localEval v) g

def IsIntegral (g : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.Sp I RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQf) (v : RepresentationTheory.Theta.AdelicSupport.PoissonAutomorphyConstruction.FinitePlace) : Prop :=
  ∀ i j, g.val i j v ∈ v.adicCompletionIntegers ℚ

theorem eventually_integral (g : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.Sp I RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQf) : ∀ᶠ v in cofinite, IsIntegral g v := by
  apply Filter.eventually_all.mpr
  intro i
  apply Filter.eventually_all.mpr
  intro j
  exact (g.val i j).property

def integralSymplectic (g : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.Sp I RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQf) (v : RepresentationTheory.Theta.AdelicSupport.PoissonAutomorphyConstruction.FinitePlace) (hg : IsIntegral g v) :
    RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.Sp I (v.adicCompletionIntegers ℚ) :=
  Local.MatrixPivot.CM.SymplecticBigCell.subringSymplectic (v.adicCompletionIntegers ℚ).toSubring (localSymplectic g v) hg

theorem integralSymplectic_map (g : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.Sp I RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQf) (v : RepresentationTheory.Theta.AdelicSupport.PoissonAutomorphyConstruction.FinitePlace) (hg : IsIntegral g v) :
    RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.mapSp (v.adicCompletionIntegers ℚ).subtype (integralSymplectic g v hg) = localSymplectic g v :=
  Local.MatrixPivot.CM.SymplecticBigCell.subringSymplectic_map (v.adicCompletionIntegers ℚ).toSubring (localSymplectic g v) hg

theorem integral_big_cell (g : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.Sp I RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQf) (v : RepresentationTheory.Theta.AdelicSupport.PoissonAutomorphyConstruction.FinitePlace) (hg : IsIntegral g v) :
    ∃ B : Matrix I I (v.adicCompletionIntegers ℚ), B.IsSymm ∧
      IsUnit ((integralSymplectic g v hg).val.toBlocks₁₁ +
        B * (integralSymplectic g v hg).val.toBlocks₂₁).det :=
  Local.MatrixPivot.CM.SymplecticBigCell.exists_symmetric (integralSymplectic g v hg)

theorem local_big_cell (g : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.Sp I RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQf) (v : RepresentationTheory.Theta.AdelicSupport.PoissonAutomorphyConstruction.FinitePlace) :
    ∃ B : Matrix I I (v.adicCompletion ℚ), B.IsSymm ∧
      IsUnit ((localSymplectic g v).val.toBlocks₁₁ +
        B * (localSymplectic g v).val.toBlocks₂₁).det :=
  Local.MatrixPivot.CM.SymplecticBigCell.exists_symmetric (localSymplectic g v)

end

end OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Finite.SymplecticLocal.CM

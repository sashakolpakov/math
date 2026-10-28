import OAI.ArithmeticGeometry.Descent.CMVariety.AbelianEndomorphism
import OAI.ArithmeticGeometry.OrdinaryLocus.Openness.Rigidity

/-! # Coefficient Parameter Point -/

namespace OAI.AlgebraicGeometry.AbelianScheme.TateComparison.CoefficientParameterPoint

noncomputable section

/-! Finite coefficient models over an algebraically closed field have
an actual ground-field point; their parameter schemes are integral. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory
open scoped Classical

variable {k : Type} [Field k] [IsAlgClosed k]

theorem integral_parameter_has_point (Y : Over (Spec (.of k)))
    [LocallyOfFiniteType Y.hom] [IsIntegral Y.left] :
    Nonempty (𝟙_ (Over (Spec (.of k))) ⟶ Y) := by
  have : JacobsonSpace Y.left := LocallyOfFiniteType.jacobsonSpace Y.hom
  obtain ⟨y, _, hy⟩ := nonempty_inter_closedPoints
    (Set.univ_nonempty : (Set.univ : Set Y.left).Nonempty) isOpen_univ.isLocallyClosed
  exact ⟨Over.homMk (pointOfClosedPoint Y.hom y hy) (pointOfClosedPoint_comp Y.hom y hy)⟩

variable (B : Type) [Field B] [Algebra k B]

open OAI.ArithmeticGeometry.Descent.CMVariety.AbelianEndomorphism

def coefficientParameter (s t : (Finset B)ᵒᵖ) : Over (Spec (.of k)) :=
  Over.mk (ArithmeticGeometry.Descent.CMVariety.AbelianEndomorphism.twoStageCoefficientBaseMap k B s t)

omit [IsAlgClosed k] in
instance coefficientParameter_integral (s t : (Finset B)ᵒᵖ) :
    IsIntegral (coefficientParameter (k := k) B s t).left :=
  inferInstanceAs (IsIntegral (Spec (.of
    (ArithmeticGeometry.Descent.CMVariety.FiniteCoefficientDiagram.Abelian.finiteCoefficientAlgebra (ArithmeticGeometry.Descent.CMVariety.FiniteCoefficientDiagram.Abelian.finiteCoefficientAlgebra k B s.unop) B t.unop))))

omit [IsAlgClosed k] in
instance coefficientParameter_finiteType (s t : (Finset B)ᵒᵖ) :
    LocallyOfFiniteType (coefficientParameter (k := k) B s t).hom :=
  ArithmeticGeometry.Descent.CMVariety.AbelianEndomorphism.twoStageCoefficientBaseMap_locallyFiniteType k B s t

def coefficientParameterPoint (s t : (Finset B)ᵒᵖ) :
    𝟙_ (Over (Spec (.of k))) ⟶ coefficientParameter (k := k) B s t :=
  (integral_parameter_has_point (coefficientParameter (k := k) B s t)).some

end

end OAI.AlgebraicGeometry.AbelianScheme.TateComparison.CoefficientParameterPoint

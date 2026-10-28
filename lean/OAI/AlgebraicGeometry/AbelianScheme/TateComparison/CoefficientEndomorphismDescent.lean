import OAI.AlgebraicGeometry.AbelianScheme.TateComparison.IteratedFamilyMaps
import OAI.AlgebraicGeometry.AbelianScheme.TateComparison.CoefficientParameterPoint

/-! # Coefficient Endomorphism Descent -/

namespace OAI.AlgebraicGeometry.AbelianScheme.TateComparison.CoefficientEndomorphismDescent

noncomputable section

/-! An endomorphism spread to two finite coefficient stages already
comes from the algebraically closed ground field, by family rigidity. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj

variable (k B : Type) [Field k] [IsAlgClosed k] [Field B] [Algebra k B]
  {g : ℕ} (A : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g (Spec (.of k))) (s t : (Finset B)ᵒᵖ)

theorem coefficient_endomorphism_descends_to_base
    (c : (ArithmeticGeometry.Descent.CMVariety.AbelianEndomorphism.twoStageCoefficientFamily k B A s t).scheme ⟶
      (ArithmeticGeometry.Descent.CMVariety.AbelianEndomorphism.twoStageCoefficientFamily k B A s t).scheme) [IsMonHom c] :
    ∃ f : A.scheme ⟶ A.scheme, IsMonHom f ∧
      ArithmeticGeometry.Descent.CMVariety.CoefficientEndomorphismComparison.Abelian.abelianPullbackEndomorphism (A.pullback (ArithmeticGeometry.Descent.CMVariety.FiniteCoefficientDiagram.Abelian.finiteCoefficientBaseMap k B s.unop))
        (ArithmeticGeometry.Descent.CMVariety.FiniteCoefficientDiagram.Abelian.finiteCoefficientBaseMap (ArithmeticGeometry.Descent.CMVariety.FiniteCoefficientDiagram.Abelian.finiteCoefficientAlgebra k B s.unop) B t.unop)
        (ArithmeticGeometry.Descent.CMVariety.CoefficientEndomorphismComparison.Abelian.abelianPullbackEndomorphism A (ArithmeticGeometry.Descent.CMVariety.FiniteCoefficientDiagram.Abelian.finiteCoefficientBaseMap k B s.unop) f) = c := by
  let p := ArithmeticGeometry.Descent.CMVariety.FiniteCoefficientDiagram.Abelian.finiteCoefficientBaseMap k B s.unop
  let h := ArithmeticGeometry.Descent.CMVariety.FiniteCoefficientDiagram.Abelian.finiteCoefficientBaseMap (ArithmeticGeometry.Descent.CMVariety.FiniteCoefficientDiagram.Abelian.finiteCoefficientAlgebra k B s.unop) B t.unop
  let c₀ : ((A.pullback p).pullback h).scheme ⟶ ((A.pullback p).pullback h).scheme := c
  have : IsMonHom c₀ := ‹IsMonHom c›
  have : LocallyOfFiniteType (h ≫ p) := ArithmeticGeometry.Descent.CMVariety.AbelianEndomorphism.twoStageCoefficientBaseMap_locallyFiniteType k B s t
  have : IsIntegral (Spec (.of
      (ArithmeticGeometry.Descent.CMVariety.FiniteCoefficientDiagram.Abelian.finiteCoefficientAlgebra (ArithmeticGeometry.Descent.CMVariety.FiniteCoefficientDiagram.Abelian.finiteCoefficientAlgebra k B s.unop) B t.unop))) := inferInstance
  exact IteratedFamilyMaps.iteratedFamily_endomorphism_descends A p h (CoefficientParameterPoint.coefficientParameterPoint B s t) c₀

end

end OAI.AlgebraicGeometry.AbelianScheme.TateComparison.CoefficientEndomorphismDescent

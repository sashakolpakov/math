import OAI.AlgebraicGeometry.Foundations.Scheme.IntegralProjective
import Mathlib.AlgebraicGeometry.Group.Abelian

/-! # CM Abelian Variety -/

namespace OAI.AlgebraicGeometry.ComplexMultiplication.CMAbelianVariety.CM

noncomputable section

/-!
# Abelian varieties in the Hodge project's geometric domain

The carrier is the project's actual integral smooth projective complex
scheme. The group law is a group object in schemes over `Spec ℂ`, so its
multiplication, inverse, and identity are algebraic morphisms over ℂ.
Commutativity is imposed on that algebraic group law.

No cohomological or cycle-algebraicity assertion is part of this bundle.
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry

/-- A complex abelian variety with a chosen projective presentation. -/
structure AbelianVariety where
  variety : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety
  [group : GrpObj variety.toOver]
  [commutative : IsCommMonObj variety.toOver]

attribute [instance] AbelianVariety.group AbelianVariety.commutative

namespace AbelianVariety

/-- The underlying object is the same genuine variety used by `hodgeConjecture`. -/
abbrev carrier (A : AbelianVariety) : Scheme := A.variety.carrier

/-- The algebraic group, viewed over the complex base. -/
abbrev toOver (A : AbelianVariety) : Over Foundations.Scheme.ProjectiveSpace.complexBase := A.variety.toOver

/-- Smoothness is inherited from the underlying projective variety. -/
instance (A : AbelianVariety) : Smooth A.variety.structureMap := inferInstance

/-- The carrier is integral, including nonemptiness and connectedness. -/
instance (A : AbelianVariety) : IsIntegral A.carrier := inferInstance

/-- Every abelian variety in this bundle has an actual closed projective embedding. -/
theorem exists_closedImmersion (A : AbelianVariety) :
    ∃ (n : ℕ) (i : A.carrier ⟶ Foundations.Scheme.ProjectiveSpace.projectiveSpace n),
      IsClosedImmersion i ∧ i ≫ Foundations.Scheme.ProjectiveSpace.projectiveSpaceToBase n = A.variety.structureMap :=
  A.variety.exists_closedImmersion

end AbelianVariety

end

end OAI.AlgebraicGeometry.ComplexMultiplication.CMAbelianVariety.CM

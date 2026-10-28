import OAI.AlgebraicGeometry.ComplexMultiplication.CMComparisonTo
import OAI.AlgebraicGeometry.ComplexMultiplication.DiagonalAction
import OAI.AlgebraicGeometry.ComplexMultiplication.FiltrationEndomorphisms
import OAI.Algebra.Homology.Notation

/-! # Endomorphisms -/

namespace OAI.AlgebraicGeometry.ComplexMultiplication

noncomputable section

open scoped OAI.AlgebraicGeometry.Hodge.Filtration.ComplexPoint

/-! # The Hodge endomorphism algebra of the original rational H¹

This algebra uses the original geometric comparison and holomorphic filtration.
It does not assert that its elements are algebraic group endomorphisms.
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry ComplexPoint
open scoped TensorProduct

variable (X : Over (Spec ↧ℂ)) [IsIntegral X.left] [Smooth X.hom]

local instance Hodge.Endomorphisms.CMHodgeEndomorphisms.localInstance1 : Algebra ℚ (Module.End ℚ H^1(X; ℚ)) :=
  Module.End.instAlgebra ℚ ℚ H^1(X; ℚ)

/-- The original geometric holomorphic filtration, pulled back to complexified rational H¹. -/
def Hodge.Endomorphisms.h1HolomorphicFiltration : Submodule ℂ (ℂ ⊗[ℚ] H^1(X; ℚ)) :=
  (ComplexPoint.Basic.ComplexSchemePoint.hodgeFiltrationComplexSubmodule X 1 1).comap (CMComparisonTo.h1ComparisonComplex X)

/-- Rational endomorphisms whose actual complexification preserves the geometric F¹. -/
def Hodge.Endomorphisms.h1HodgeEndomorphismAlgebra : Subalgebra ℚ (Module.End ℚ H^1(X; ℚ)) :=
  FiltrationEndomorphisms.filtrationEndomorphismAlgebra (Hodge.Endomorphisms.h1HolomorphicFiltration X)

local instance Hodge.Endomorphisms.CMHodgeEndomorphisms.localInstance2 : Ring (Hodge.Endomorphisms.h1HodgeEndomorphismAlgebra X) :=
  Subalgebra.toRing (Hodge.Endomorphisms.h1HodgeEndomorphismAlgebra X)

local instance Hodge.Endomorphisms.CMHodgeEndomorphisms.localInstance3 : Algebra ℚ (Hodge.Endomorphisms.h1HodgeEndomorphismAlgebra X) :=
  Subalgebra.algebra (Hodge.Endomorphisms.h1HodgeEndomorphismAlgebra X)

/-- For the original diagonal action, the algebra membership condition is exactly
the filtration condition already used in `CMH1Data`. -/
theorem Hodge.Endomorphisms.diagonalAction_mem_h1HodgeEndomorphismAlgebra
    (d : Definitions.CMH1Data X) (a : (i : Fin d.factors) → d.field i) :
    Definitions.diagonalAction d.field d.model a ∈ Hodge.Endomorphisms.h1HodgeEndomorphismAlgebra X := by
  intro z hz
  change Definitions.h1Comparison X ((Definitions.diagonalAction d.field d.model a).baseChange ℂ z) ∈
    ComplexPoint.Basic.ComplexSchemePoint.hodgeFiltrationComplexSubmodule X 1 1
  exact d.preserves_hodgeFiltration a z hz

/-- The original CM data give an embedding of the whole CM-field product into the
original Hodge endomorphism algebra. Algebraic realization is a separate theorem. -/
def Definitions.CMH1Data.hodgeEndomorphismEmbedding (d : Definitions.CMH1Data X) :
    ((i : Fin d.factors) → d.field i) →ₐ[ℚ] Hodge.Endomorphisms.h1HodgeEndomorphismAlgebra X :=
  (DiagonalAction.diagonalActionAlgHom d.field d.model).codRestrict (Hodge.Endomorphisms.h1HodgeEndomorphismAlgebra X)
    (Hodge.Endomorphisms.diagonalAction_mem_h1HodgeEndomorphismAlgebra X d)

/-- Faithfulness follows from the original rank-one model, including all field factors. -/
theorem Definitions.CMH1Data.hodgeEndomorphismEmbedding_injective (d : Definitions.CMH1Data X) :
    Function.Injective (d.hodgeEndomorphismEmbedding X) := by
  intro a b h
  exact DiagonalAction.diagonalActionAlgHom_injective d.field d.model (congrArg Subtype.val h)

end

end OAI.AlgebraicGeometry.ComplexMultiplication

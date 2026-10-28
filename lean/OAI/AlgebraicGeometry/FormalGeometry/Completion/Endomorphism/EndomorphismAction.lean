import OAI.AlgebraicGeometry.FormalGeometry.Completion.Geometric.Primitivity
import OAI.AlgebraicGeometry.FormalGeometry.Completion.PrimitiveAction

/-! # Endomorphism Action -/

namespace OAI.AlgebraicGeometry.FormalGeometry.Completion.Endomorphism.EndomorphismAction.Construction

noncomputable section

/-! The actual rational opposite endomorphism algebra acts on the full geometric H¹. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped TensorProduct

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

universe u

variable (ℓ : ℕ) [Fact ℓ.Prime] (k : Type u) [Field k]
  (A : Over (Spec (CommRingCat.of k))) [GrpObj A] [IsCommMonObj A]
  [IsProper A.hom] [Smooth A.hom] [GeometricallyIntegral A.hom]

/-- Actual group-scheme addition induces addition of pullbacks on all geometric H¹. -/
theorem geometricH1Pullback_add (f g : Endomorphisms.Construction.AlgebraicEnd A) :
    Action.Construction.geometricH1Pullback ℓ k (f + g).toMul.hom.hom =
      Action.Construction.geometricH1Pullback ℓ k f.toMul.hom.hom + Action.Construction.geometricH1Pullback ℓ k g.toMul.hom.hom := by
  apply sub_eq_zero.mp
  rw [GroupLawCohomology.Construction.geometricH1Pullback_add_defect, Geometric.Primitivity.Construction.geometricH1GroupLawDefect_eq_zero, LinearMap.comp_zero]

local instance fullH1EndRing : Ring (Module.End (AlgebraicClosure ℚ_[ℓ]) (Cohomology.Construction.GeometricH1 ℓ A)) :=
  Module.End.instRing (R := AlgebraicClosure ℚ_[ℓ]) (N₁ := Cohomology.Construction.GeometricH1 ℓ A)

/-- The actual opposite endomorphism ring acts on the full H¹ by pullback. -/
def algebraicEndOppH1RingHom :
    (Endomorphisms.Construction.AlgebraicEnd A)ᵐᵒᵖ →+* Module.End (AlgebraicClosure ℚ_[ℓ]) (Cohomology.Construction.GeometricH1 ℓ A) :=
  RingHom.mk' (α := (Endomorphisms.Construction.AlgebraicEnd A)ᵐᵒᵖ)
    (β := Module.End (AlgebraicClosure ℚ_[ℓ]) (Cohomology.Construction.GeometricH1 ℓ A))
    (Action.Construction.algebraicEndOppH1MonoidHom ℓ k A)
    (fun f g => geometricH1Pullback_add ℓ k A f.unop g.unop)

def algebraicEndOppH1IntAlgHom :
    (Endomorphisms.Construction.AlgebraicEnd A)ᵐᵒᵖ →ₐ[ℤ] Module.End (AlgebraicClosure ℚ_[ℓ]) (Cohomology.Construction.GeometricH1 ℓ A) where
  __ := algebraicEndOppH1RingHom ℓ k A
  commutes' r := by
    simpa only [algebraMap_int_eq] using! map_intCast (algebraicEndOppH1RingHom ℓ k A) r

/-- Rationalization of the proved action on the entire actual geometric H¹. -/
def rationalAlgebraicEndOppH1Action :
    (Endomorphisms.Construction.RationalAlgebraicEnd A)ᵐᵒᵖ →ₐ[ℚ]
      Module.End (AlgebraicClosure ℚ_[ℓ]) (Cohomology.Construction.GeometricH1 ℓ A) :=
  AlgHom.opComm ((AlgHom.liftEquiv ℤ ℚ (Endomorphisms.Construction.AlgebraicEnd A)
    (Module.End (AlgebraicClosure ℚ_[ℓ]) (Cohomology.Construction.GeometricH1 ℓ A))ᵐᵒᵖ)
      (AlgHom.opComm.symm (algebraicEndOppH1IntAlgHom ℓ k A)))

theorem rationalAlgebraicEndOppH1Action_tmul (r : ℚ) (f : Endomorphisms.Construction.AlgebraicEnd A) :
    rationalAlgebraicEndOppH1Action ℓ k A (MulOpposite.op (r ⊗ₜ[ℤ] f)) =
      r • algebraicEndOppH1RingHom ℓ k A (MulOpposite.op f) := rfl

variable [Fintype k]

/-- Rational Frobenius acts as the actual geometric Frobenius operator on all H¹. -/
theorem rationalAlgebraicEndOppH1Action_frobenius :
    rationalAlgebraicEndOppH1Action ℓ k A (MulOpposite.op (Endomorphisms.Construction.rationalAlgebraicFrobenius k A)) =
      CohomologyPullback.Construction.geometricH1Frobenius ℓ k A := by
  rw [Endomorphisms.Construction.rationalAlgebraicFrobenius, rationalAlgebraicEndOppH1Action_tmul, one_smul]
  rfl

/-- The full rational action preserves centrality of the actual Frobenius. -/
theorem rationalAlgebraicEndOppH1Action_frobenius_commutes
    (x : (Endomorphisms.Construction.RationalAlgebraicEnd A)ᵐᵒᵖ) :
    Commute (CohomologyPullback.Construction.geometricH1Frobenius ℓ k A) (rationalAlgebraicEndOppH1Action ℓ k A x) := by
  rw [← rationalAlgebraicEndOppH1Action_frobenius]
  exact ((Endomorphisms.Construction.rationalAlgebraicFrobenius_commutes k A x.unop).op).map
    (rationalAlgebraicEndOppH1Action ℓ k A)

end

end OAI.AlgebraicGeometry.FormalGeometry.Completion.Endomorphism.EndomorphismAction.Construction

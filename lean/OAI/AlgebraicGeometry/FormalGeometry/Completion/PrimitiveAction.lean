import OAI.AlgebraicGeometry.FormalGeometry.Completion.GroupLawCohomology
import Mathlib.Algebra.Algebra.Opposite

/-! # Primitive Action -/

namespace OAI.AlgebraicGeometry.FormalGeometry.Completion.PrimitiveAction.Construction

noncomputable section

/-!
# Completion: endomorphisms act additively on primitive geometric H¹

This action is on the kernel of the group-law defect in the genuine H¹.
The assertion that this kernel is all H¹ is a separate geometric obligation.
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry MonoidalCategory
open scoped TensorProduct

universe u

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

variable (ℓ : ℕ) [Fact ℓ.Prime] (k : Type u) [Field k]
    {A B : Over (Spec (CommRingCat.of k))} [GrpObj A] [GrpObj B]

/-- Actual group-scheme pullbacks preserve primitive classes. -/
def primitiveGeometricH1Pullback (f : A ⟶ B) [IsMonHom f] :
    GroupLawCohomology.Construction.PrimitiveGeometricH1 ℓ k B →ₗ[AlgebraicClosure ℚ_[ℓ]] GroupLawCohomology.Construction.PrimitiveGeometricH1 ℓ k A where
  toFun x := ⟨Endomorphism.Action.Construction.geometricH1Pullback ℓ k f x.val, by
    change GroupLawCohomology.Construction.geometricH1GroupLawDefect ℓ k A (Endomorphism.Action.Construction.geometricH1Pullback ℓ k f x.val) = 0
    have h := congrArg (fun F => F x.val) (GroupLawCohomology.Construction.geometricH1GroupLawDefect_naturality ℓ k f)
    change _ = Endomorphism.Action.Construction.geometricH1Pullback ℓ k (f ⊗ₘ f) (GroupLawCohomology.Construction.geometricH1GroupLawDefect ℓ k B x.val) at h
    exact h.trans (by rw [show GroupLawCohomology.Construction.geometricH1GroupLawDefect ℓ k B x.val = 0 from x.property,
      map_zero])⟩
  map_add' x y := Subtype.ext (map_add (Endomorphism.Action.Construction.geometricH1Pullback ℓ k f) x.val y.val)
  map_smul' r x := Subtype.ext (map_smul (Endomorphism.Action.Construction.geometricH1Pullback ℓ k f) r x.val)

variable (A) [IsCommMonObj A]

local instance primitiveEndRing :
  Ring (Module.End (AlgebraicClosure ℚ_[ℓ]) (GroupLawCohomology.Construction.PrimitiveGeometricH1 ℓ k A)) :=
  Module.End.instRing (R := AlgebraicClosure ℚ_[ℓ]) (N₁ := GroupLawCohomology.Construction.PrimitiveGeometricH1 ℓ k A)

/-- The opposite endomorphism monoid acts on primitive classes by restriction. -/
def algebraicEndOppPrimitiveH1MonoidHom :
    (Endomorphisms.Construction.AlgebraicEnd A)ᵐᵒᵖ →*
      Module.End (AlgebraicClosure ℚ_[ℓ]) (GroupLawCohomology.Construction.PrimitiveGeometricH1 ℓ k A) where
  toFun f := primitiveGeometricH1Pullback ℓ k f.unop.toMul.hom.hom
  map_one' := by
    apply LinearMap.ext
    intro x
    apply Subtype.ext
    exact congrArg (fun F => F x.val) (Endomorphism.Action.Construction.geometricH1Pullback_id ℓ k A)
  map_mul' f g := by
    apply LinearMap.ext
    intro x
    apply Subtype.ext
    exact congrArg (fun F => F x.val) ((Endomorphism.Action.Construction.algebraicEndOppH1MonoidHom ℓ k A).map_mul f g)

/-- Addition is proved from the group-law formula, not supplied as action data. -/
def algebraicEndOppPrimitiveH1RingHom :
    (Endomorphisms.Construction.AlgebraicEnd A)ᵐᵒᵖ →+*
      Module.End (AlgebraicClosure ℚ_[ℓ]) (GroupLawCohomology.Construction.PrimitiveGeometricH1 ℓ k A) :=
  RingHom.mk' (α := (Endomorphisms.Construction.AlgebraicEnd A)ᵐᵒᵖ)
    (β := Module.End (AlgebraicClosure ℚ_[ℓ]) (GroupLawCohomology.Construction.PrimitiveGeometricH1 ℓ k A))
    (algebraicEndOppPrimitiveH1MonoidHom ℓ k A) (fun f g => by
    exact LinearMap.ext (fun x : GroupLawCohomology.Construction.PrimitiveGeometricH1 ℓ k A =>
      Subtype.ext (GroupLawCohomology.Construction.geometricH1Pullback_add_on_primitive ℓ k A f.unop g.unop x)))

def algebraicEndOppPrimitiveH1IntAlgHom :
    (Endomorphisms.Construction.AlgebraicEnd A)ᵐᵒᵖ →ₐ[ℤ]
      Module.End (AlgebraicClosure ℚ_[ℓ]) (GroupLawCohomology.Construction.PrimitiveGeometricH1 ℓ k A) where
  __ := algebraicEndOppPrimitiveH1RingHom ℓ k A
  commutes' r := by
    simpa only [algebraMap_int_eq] using! map_intCast (algebraicEndOppPrimitiveH1RingHom ℓ k A) r

/-- Rationalization of the genuine opposite endomorphism action on primitive classes. -/
def rationalAlgebraicEndOppPrimitiveH1Action :
    (Endomorphisms.Construction.RationalAlgebraicEnd A)ᵐᵒᵖ →ₐ[ℚ]
      Module.End (AlgebraicClosure ℚ_[ℓ]) (GroupLawCohomology.Construction.PrimitiveGeometricH1 ℓ k A) :=
  AlgHom.opComm ((AlgHom.liftEquiv ℤ ℚ (Endomorphisms.Construction.AlgebraicEnd A)
    (Module.End (AlgebraicClosure ℚ_[ℓ]) (GroupLawCohomology.Construction.PrimitiveGeometricH1 ℓ k A))ᵐᵒᵖ)
      (AlgHom.opComm.symm (algebraicEndOppPrimitiveH1IntAlgHom ℓ k A)))

theorem rationalAlgebraicEndOppPrimitiveH1Action_tmul (r : ℚ) (f : Endomorphisms.Construction.AlgebraicEnd A) :
    rationalAlgebraicEndOppPrimitiveH1Action ℓ k A (MulOpposite.op (r ⊗ₜ[ℤ] f)) =
      r • algebraicEndOppPrimitiveH1RingHom ℓ k A (MulOpposite.op f) := rfl

variable [Fintype k]

/-- This rational action retains the existing geometric Frobenius on primitive classes. -/
theorem rationalAlgebraicEndOppPrimitiveH1Action_frobenius
    (x : GroupLawCohomology.Construction.PrimitiveGeometricH1 ℓ k A) :
    (rationalAlgebraicEndOppPrimitiveH1Action ℓ k A
      (MulOpposite.op (Endomorphisms.Construction.rationalAlgebraicFrobenius k A)) x).val =
        CohomologyPullback.Construction.geometricH1Frobenius ℓ k A x.val := by
  rw [Endomorphisms.Construction.rationalAlgebraicFrobenius, rationalAlgebraicEndOppPrimitiveH1Action_tmul, one_smul]
  rfl

/-- Centrality of rational Frobenius is retained by the primitive rational action. -/
theorem rationalAlgebraicEndOppPrimitiveH1Action_frobenius_commutes
    (x : (Endomorphisms.Construction.RationalAlgebraicEnd A)ᵐᵒᵖ) :
    Commute (rationalAlgebraicEndOppPrimitiveH1Action ℓ k A
      (MulOpposite.op (Endomorphisms.Construction.rationalAlgebraicFrobenius k A)))
      (rationalAlgebraicEndOppPrimitiveH1Action ℓ k A x) :=
  ((Endomorphisms.Construction.rationalAlgebraicFrobenius_commutes k A x.unop).op).map
    (rationalAlgebraicEndOppPrimitiveH1Action ℓ k A)

end

end OAI.AlgebraicGeometry.FormalGeometry.Completion.PrimitiveAction.Construction

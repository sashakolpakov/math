import OAI.AlgebraicGeometry.Isogenies.NeighborCounting.IdentityLineCoordinates
import OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Evaluated.ComponentSurjectivity

/-! # Generic Point Coordinates -/

namespace OAI.AlgebraicGeometry.Isogenies.NeighborCounting.GenericPointCoordinates.Lifts

noncomputable section

/-! Generic linear coordinates are constructed on the actual torsion
points. Their module law follows from the q-torsion equation, and rank
three follows from the native block's q^3 cardinality. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj

variable (R L : Type) [CommRing R] [Field L] [Algebra R L]
variable (q : ℕ) [Fact q.Prime]
variable (A : Over (Spec (.of R))) [GrpObj A] [IsCommMonObj A]

abbrev GenericPointSpace := Additive (Evaluated.Sections.Lifts.genericTest R L ⟶ A)

abbrev genericPointModule (hk : ∀ a : Evaluated.Sections.Lifts.genericTest R L ⟶ A, a ^ q = 1) :
    Module (ZMod q) (GenericPointSpace R L A) :=
  AddCommGroup.zmodModule (fun a ↦ hk a.toMul)

def genericPointCoordinates :
    (Evaluated.Sections.Lifts.genericTest R L ⟶ A) ≃* Multiplicative (GenericPointSpace R L A) where
  toFun a := Multiplicative.ofAdd (Additive.ofMul a)
  invFun a := a.toAdd.toMul
  left_inv _ := rfl
  right_inv _ := rfl
  map_mul' _ _ := rfl

variable (hk : ∀ a : Evaluated.Sections.Lifts.genericTest R L ⟶ A, a ^ q = 1)
variable (hcard : Nat.card (Evaluated.Sections.Lifts.genericTest R L ⟶ A) = q ^ 3)

include hcard in
omit [GrpObj A] [IsCommMonObj A] in
theorem genericPointSpace_finite : Finite (GenericPointSpace R L A) :=
  Nat.finite_of_card_ne_zero (by
    change Nat.card (Evaluated.Sections.Lifts.genericTest R L ⟶ A) ≠ 0
    rw [hcard]
    exact pow_ne_zero _ (Fact.out : q.Prime).ne_zero)

include hcard in
theorem genericPointSpace_finrank :
    letI := genericPointModule R L q A hk
    Module.finrank (ZMod q) (GenericPointSpace R L A) = 3 := by
  let := genericPointModule R L q A hk
  have : Finite (GenericPointSpace R L A) := genericPointSpace_finite R L q A hcard
  have hfinite : Module.Finite (ZMod q) (GenericPointSpace R L A) := Module.Finite.of_finite
  apply Nat.pow_right_injective (Fact.out : q.Prime).two_le
  have h : Nat.card (GenericPointSpace R L A) =
      Nat.card (ZMod q) ^ Module.finrank (ZMod q) (GenericPointSpace R L A) :=
    @Module.natCard_eq_pow_finrank (ZMod q) (GenericPointSpace R L A)
      inferInstance inferInstance (genericPointModule R L q A hk) hfinite
  rw [Nat.card_zmod] at h
  exact h.symm.trans hcard

attribute [local instance] Picard.PoincareBundle.Kernel.Scheme.kernelGroup

variable {I : Type}
variable (π : A ⟶ (AbelianScheme.FrobeniusKernel.EtaleSubgroups.Construction.etaleGroupScheme (Spec (.of R)) (Multiplicative (Fin 2 → ZMod q))).X)
  [IsMonHom π] [Surjective π.left]
variable (eA : AbelianModuli.HilbertConstruction.ConstantScheme.Iff.constantScheme (Spec (.of L)) I ≅
  (Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap R L)))).obj A)

/-- The identity-part coordinate is an output of the rank calculation
and evaluated component surjectivity, with no coordinate basis input. -/
def constructedIdentityCoordinates :
    (Evaluated.Sections.Lifts.genericTest R L ⟶ Picard.PoincareBundle.Kernel.Scheme.kernelObject π) ≃* Multiplicative (ZMod q) := by
  letI := genericPointModule R L q A hk
  have : Finite (GenericPointSpace R L A) := genericPointSpace_finite R L q A hcard
  have hfinite : Module.Finite (ZMod q) (GenericPointSpace R L A) := Module.Finite.of_finite
  exact @IdentityLineCoordinates.Lifts.identityLineCoordinates R L _ _ _ q _ (GenericPointSpace R L A) (Fin 2 → ZMod q)
    _ (genericPointModule R L q A hk) _ _ A _ (genericPointCoordinates R L A) π _ hfinite
    (Evaluated.ComponentSurjectivity.Lifts.evaluated_component_points_surjective R L π eA)
    (genericPointSpace_finrank R L q A hk hcard) (by simp)

end

end OAI.AlgebraicGeometry.Isogenies.NeighborCounting.GenericPointCoordinates.Lifts

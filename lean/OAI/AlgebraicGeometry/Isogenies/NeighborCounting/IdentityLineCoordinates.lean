import OAI.AlgebraicGeometry.Isogenies.NeighborCounting.GenericComponentSection
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-! # Identity Line Coordinates -/

namespace OAI.AlgebraicGeometry.Isogenies.NeighborCounting.IdentityLineCoordinates.Lifts

noncomputable section

/-!
Construct the generic coordinate of the identity-part kernel from the
actual component projection. Rank three minus the rank-two etale quotient
gives the line used in the graph count; its coordinate is not an input.
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj

open OAI.AlgebraicGeometry.Picard.PoincareBundle.Kernel.Scheme

attribute [local instance] Picard.PoincareBundle.Kernel.Scheme.kernelGroup

variable (R L : Type) [CommRing R] [Field L] [Algebra R L]
variable (q : ℕ) [Fact q.Prime]
variable {V W : Type} [AddCommGroup V] [Module (ZMod q) V]
  [AddCommGroup W] [Module (ZMod q) W]
variable (A : Over (Spec (.of R))) [GrpObj A]
variable (c : (Evaluated.Sections.Lifts.genericTest R L ⟶ A) ≃* Multiplicative V)
variable (π : A ⟶ (AbelianScheme.FrobeniusKernel.EtaleSubgroups.Construction.etaleGroupScheme (Spec (.of R)) (Multiplicative W)).X) [IsMonHom π]

theorem genericComponentLinear_zero_iff (v : V) :
    GenericComponentSection.Lifts.genericComponentLinear R L q A c π v = 0 ↔ c.symm (Multiplicative.ofAdd v) ≫ π = 1 := by
  change Evaluated.Characters.Lifts.genericConstantCoordinates R L (Multiplicative W)
    (c.symm (Multiplicative.ofAdd v) ≫ π) = 1 ↔ _
  rw [← (Evaluated.Characters.Lifts.genericConstantCoordinates R L (Multiplicative W)).map_one]
  exact (Evaluated.Characters.Lifts.genericConstantCoordinates R L (Multiplicative W)).injective.eq_iff

/-- Generic points of the actual scheme-theoretic kernel have exactly
the linear kernel coordinates. -/
def genericKernelCoordinates :
    (Evaluated.Sections.Lifts.genericTest R L ⟶ Picard.PoincareBundle.Kernel.Scheme.kernelObject π) ≃*
      Multiplicative (LinearMap.ker (GenericComponentSection.Lifts.genericComponentLinear R L q A c π)) where
  toFun a := Multiplicative.ofAdd ⟨(c (a ≫ Picard.PoincareBundle.Kernel.Scheme.kernelInclusion π)).toAdd, by
    apply (genericComponentLinear_zero_iff R L q A c π _).mpr
    change c.symm (c (a ≫ Picard.PoincareBundle.Kernel.Scheme.kernelInclusion π)) ≫ π = 1
    rw [c.symm_apply_apply, Category.assoc, Picard.PoincareBundle.Kernel.Scheme.kernelInclusion_comp, MonObj.comp_one]⟩
  invFun v := (Picard.PoincareBundle.Kernel.Scheme.kernelPointsEquiv π (Evaluated.Sections.Lifts.genericTest R L)).symm
    ⟨c.symm (Multiplicative.ofAdd v.toAdd.val),
      (genericComponentLinear_zero_iff R L q A c π v.toAdd.val).mp v.toAdd.property⟩
  left_inv a := by
    apply (Picard.PoincareBundle.Kernel.Scheme.kernelPointsEquiv π (Evaluated.Sections.Lifts.genericTest R L)).injective
    apply Subtype.ext
    change ((Picard.PoincareBundle.Kernel.Scheme.kernelPointsEquiv π (Evaluated.Sections.Lifts.genericTest R L))
      ((Picard.PoincareBundle.Kernel.Scheme.kernelPointsEquiv π (Evaluated.Sections.Lifts.genericTest R L)).symm _)).val = a ≫ Picard.PoincareBundle.Kernel.Scheme.kernelInclusion π
    rw [Equiv.apply_symm_apply]
    exact c.symm_apply_apply _
  right_inv v := by
    apply Multiplicative.ext
    apply Subtype.ext
    change (c (((Picard.PoincareBundle.Kernel.Scheme.kernelPointsEquiv π (Evaluated.Sections.Lifts.genericTest R L)).symm
      ⟨c.symm (Multiplicative.ofAdd v.toAdd.val), _⟩) ≫ Picard.PoincareBundle.Kernel.Scheme.kernelInclusion π)).toAdd = v.toAdd.val
    have h := congrArg Subtype.val ((Picard.PoincareBundle.Kernel.Scheme.kernelPointsEquiv π (Evaluated.Sections.Lifts.genericTest R L)).apply_symm_apply
      ⟨c.symm (Multiplicative.ofAdd v.toAdd.val),
        (genericComponentLinear_zero_iff R L q A c π v.toAdd.val).mp v.toAdd.property⟩)
    change _ ≫ Picard.PoincareBundle.Kernel.Scheme.kernelInclusion π = c.symm (Multiplicative.ofAdd v.toAdd.val) at h
    rw [h, c.apply_symm_apply]
    rfl
  map_mul' a b := by
    apply Multiplicative.ext
    apply Subtype.ext
    change (c ((a * b) ≫ Picard.PoincareBundle.Kernel.Scheme.kernelInclusion π)).toAdd =
      (c (a ≫ Picard.PoincareBundle.Kernel.Scheme.kernelInclusion π)).toAdd + (c (b ≫ Picard.PoincareBundle.Kernel.Scheme.kernelInclusion π)).toAdd
    rw [MonObj.mul_comp, c.map_mul]
    rfl

variable [FiniteDimensional (ZMod q) V]
variable (hπ : Function.Surjective (fun a : Evaluated.Sections.Lifts.genericTest R L ⟶ A => a ≫ π))
variable (hV : Module.finrank (ZMod q) V = 3) (hW : Module.finrank (ZMod q) W = 2)

include hπ hV hW in
theorem genericKernel_finrank_one :
    Module.finrank (ZMod q) (LinearMap.ker (GenericComponentSection.Lifts.genericComponentLinear R L q A c π)) = 1 := by
  have h := (GenericComponentSection.Lifts.genericComponentLinear R L q A c π).finrank_range_add_finrank_ker
  rw [LinearMap.range_eq_top.mpr (GenericComponentSection.Lifts.genericComponentLinear_surjective R L q A c π hπ),
    finrank_top, hV, hW] at h
  omega

/-- The coordinate on the rank-one identity-part generic kernel is
constructed by the dimension calculation above. -/
def identityLineCoordinates : (Evaluated.Sections.Lifts.genericTest R L ⟶ Picard.PoincareBundle.Kernel.Scheme.kernelObject π) ≃* Multiplicative (ZMod q) :=
  (genericKernelCoordinates R L q A c π).trans
    (AddEquiv.toMultiplicative
      (LinearEquiv.ofFinrankEq (R := ZMod q) (LinearMap.ker (GenericComponentSection.Lifts.genericComponentLinear R L q A c π))
        (ZMod q) (by
          rw [genericKernel_finrank_one R L q A c π hπ hV hW, Module.finrank_self])).toAddEquiv)

end

end OAI.AlgebraicGeometry.Isogenies.NeighborCounting.IdentityLineCoordinates.Lifts

import OAI.AlgebraicGeometry.AbelianScheme.TateComparison.PELCoherence

/-! # Polarization Type Transport -/

namespace OAI.AlgebraicGeometry.AbelianScheme.TateComparison

noncomputable section

/-! Polarization type is invariant under a genuine PEL-family
isomorphism: both finite-flat degree and the actual geometric kernel
are transported by the commuting polarization square. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj BigOperators

universe u
variable {R : Type u} [CommRing R] {S : Scheme.{u}} {g N : ℕ}
  {P Q : PEL.PELFamilyData R g N S} (e : PELModuli.PELFamilyIso P Q)

def PELModuli.PELFamilyIso.polarizationKernelMap (T : Over S) :
    P.polarizationMap.kernelAt T →* Q.polarizationMap.kernelAt T where
  toFun x := ⟨x.val ≫ e.abelian.hom, by
    change (x.val ≫ e.abelian.hom) ≫ Q.polarizationMap.hom = 1
    rw [Category.assoc, ← e.polarization, ← Category.assoc]
    rw [show x.val ≫ P.polarizationMap.hom = 1 from x.property, MonObj.one_comp]⟩
  map_one' := Subtype.ext (MonObj.one_comp e.abelian.hom)
  map_mul' x y := Subtype.ext (MonObj.mul_comp x.val y.val e.abelian.hom)

def PELModuli.PELFamilyIso.polarizationKernelEquiv (T : Over S) :
    P.polarizationMap.kernelAt T ≃* Q.polarizationMap.kernelAt T where
  __ := e.polarizationKernelMap T
  invFun := e.symm.polarizationKernelMap T
  left_inv x := by
    apply Subtype.ext
    change (x.val ≫ e.abelian.hom) ≫ e.abelian.inv = x.val
    simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id]
  right_inv x := by
    apply Subtype.ext
    change (x.val ≫ e.abelian.inv) ≫ e.abelian.hom = x.val
    simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]

include e in
theorem PELModuli.PELFamilyIso.polarizationType (δ : Fin g → ℕ)
    (h : Q.polarizationMap.HasPolarizationType δ) : P.polarizationMap.HasPolarizationType δ where
  degree z := by
    have : IsIso e.abelian.hom.left :=
      inferInstanceAs (IsIso ((Over.forget S).map e.abelian.hom))
    have : IsIso e.dual.hom.left :=
      inferInstanceAs (IsIso ((Over.forget S).map e.dual.hom))
    have hcart : IsPullback e.abelian.hom.left P.polarizationMap.hom.left
        Q.polarizationMap.hom.left e.dual.hom.left :=
      IsPullback.of_horiz_isIso ⟨congrArg (fun f => f.left) e.polarization.symm⟩
    exact (Scheme.Hom.finrank_of_isPullback _ _ _ _ hcart z).trans (h.degree (e.dual.hom.left z))
  geometricKernel k _ _ b := by
    obtain ⟨c⟩ := h.geometricKernel k b
    exact ⟨(e.polarizationKernelEquiv (Over.mk b)).trans c⟩

end

end OAI.AlgebraicGeometry.AbelianScheme.TateComparison

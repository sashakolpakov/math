import OAI.AlgebraicGeometry.Resolution.Blowups.ComaximalFactorBoundaryCenter
import OAI.AlgebraicGeometry.Resolution.Blowups.Smooth.CenterComponents

/-! # Component Boundary Atlas -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups

noncomputable section

/-! Every individual integral component of a smooth center inherits its actual boundary atlas. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace

universe u v

theorem Smooth.ComponentBoundaryAtlas.Construction.idealSheaf_sup_finset_prod_eq_top {X : Scheme.{u}} {ι : Type v}
    (K : X.IdealSheafData) (D : ι → X.IdealSheafData) (S : Finset ι)
    (h : ∀ j ∈ S, K ⊔ D j = ⊤) : K ⊔ ∏ j ∈ S, D j = ⊤ := by
  ext1
  funext U
  change K.ideal U ⊔ (∏ j ∈ S, D j).ideal U = ⊤
  rw [Global.MixedBoundary.Construction.idealSheaf_finset_prod_ideal]
  apply Ideal.isCoprime_iff_sup_eq.mp
  apply IsCoprime.prod_right
  intro j hj
  apply Ideal.isCoprime_iff_sup_eq.mpr
  exact congrArg (fun L : X.IdealSheafData => L.ideal U) (h j hj)

variable {X : Scheme} (f : X ⟶ Foundations.Scheme.ProjectiveSpace.complexBase) (I : X.IdealSheafData)
    [Smooth (I.subschemeι ≫ f)] [Fintype (irreducibleComponents I.subscheme)]

def Smooth.ComponentBoundaryAtlas.Construction.smoothCenterOtherComponents (C : irreducibleComponents I.subscheme) : X.IdealSheafData := by
  classical
  exact ∏ D ∈ Finset.univ.erase C, Blowups.Smooth.CenterComponents.Construction.smoothCenterComponentIdeal f I D

theorem Smooth.ComponentBoundaryAtlas.Construction.smoothCenterComponent_factorization (C : irreducibleComponents I.subscheme) :
    I = Blowups.Smooth.CenterComponents.Construction.smoothCenterComponentIdeal f I C * Blowups.Smooth.ComponentBoundaryAtlas.Construction.smoothCenterOtherComponents f I C := by
  classical
  unfold Blowups.Smooth.ComponentBoundaryAtlas.Construction.smoothCenterOtherComponents
  rw [Finset.mul_prod_erase _ _ (Finset.mem_univ C), Blowups.Smooth.CenterComponents.Construction.smoothCenterComponentIdeal_prod]

theorem Smooth.ComponentBoundaryAtlas.Construction.smoothCenterComponent_other_sup (C : irreducibleComponents I.subscheme) :
    Blowups.Smooth.CenterComponents.Construction.smoothCenterComponentIdeal f I C ⊔ Blowups.Smooth.ComponentBoundaryAtlas.Construction.smoothCenterOtherComponents f I C = ⊤ := by
  classical
  apply Blowups.Smooth.ComponentBoundaryAtlas.Construction.idealSheaf_sup_finset_prod_eq_top
  intro D hD
  exact Blowups.Smooth.CenterComponents.Construction.smoothCenterComponentIdeal_sup f I C D (fun h => (Finset.mem_erase.mp hD).1 h.symm)

def Global.CanonicalBoundaryAtlas.Construction.GlobalMixedCenterAtlas.integralComponent
    {β : Type} {D : β → X.IdealSheafData} (A : Global.CanonicalBoundaryAtlas.Construction.GlobalMixedCenterAtlas f I D)
    (C : irreducibleComponents I.subscheme) :
    Global.CanonicalBoundaryAtlas.Construction.GlobalMixedCenterAtlas f (Blowups.Smooth.CenterComponents.Construction.smoothCenterComponentIdeal f I C) D :=
  A.comaximalFactor (Blowups.Smooth.CenterComponents.Construction.smoothCenterComponentIdeal f I C) (Blowups.Smooth.ComponentBoundaryAtlas.Construction.smoothCenterOtherComponents f I C)
    (Blowups.Smooth.ComponentBoundaryAtlas.Construction.smoothCenterComponent_factorization f I C) (Blowups.Smooth.ComponentBoundaryAtlas.Construction.smoothCenterComponent_other_sup f I C)

end

end OAI.AlgebraicGeometry.Resolution.Blowups

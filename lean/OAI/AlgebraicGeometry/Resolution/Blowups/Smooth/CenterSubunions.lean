import OAI.AlgebraicGeometry.Resolution.Blowups.Smooth.ComponentBoundaryAtlas
import OAI.AlgebraicGeometry.Resolution.Blowups.Smooth.ComaximalFactor
import OAI.AlgebraicGeometry.Resolution.Blowups.Integral.IdealSheafProducts

/-! # Center Subunions -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups

noncomputable section

/-! Finite unions of smooth center components are actual smooth comaximal subcenters with their boundary charts. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace

variable {X : Scheme} (f : X ⟶ Foundations.Scheme.ProjectiveSpace.complexBase) (I : X.IdealSheafData)
    [Smooth (I.subschemeι ≫ f)]

def Smooth.CenterSubunions.Construction.smoothCenterSubunionIdeal (s : Finset (irreducibleComponents I.subscheme)) : X.IdealSheafData :=
  ∏ C ∈ s, Blowups.Smooth.CenterComponents.Construction.smoothCenterComponentIdeal f I C

theorem Smooth.CenterSubunions.Construction.smoothCenterSubunionIdeal_disjoint
    (s t : Finset (irreducibleComponents I.subscheme)) (hst : Disjoint s t) :
    Blowups.Smooth.CenterSubunions.Construction.smoothCenterSubunionIdeal f I s ⊔ Blowups.Smooth.CenterSubunions.Construction.smoothCenterSubunionIdeal f I t = ⊤ := by
  classical
  apply Blowups.Smooth.ComponentBoundaryAtlas.Construction.idealSheaf_sup_finset_prod_eq_top
  intro D hD
  rw [sup_comm]
  apply Blowups.Smooth.ComponentBoundaryAtlas.Construction.idealSheaf_sup_finset_prod_eq_top
  intro C hC
  exact Blowups.Smooth.CenterComponents.Construction.smoothCenterComponentIdeal_sup f I D C (fun he =>
    Finset.disjoint_left.mp hst hC (he ▸ hD))

theorem Smooth.CenterSubunions.Construction.smoothCenterSubunionIdeal_ne_bot (hI : I ≠ ⊥)
    (s : Finset (irreducibleComponents I.subscheme)) [IsIntegral X] [IsLocallyNoetherian X] :
    Blowups.Smooth.CenterSubunions.Construction.smoothCenterSubunionIdeal f I s ≠ ⊥ :=
  Integral.IdealSheafProducts.Construction.idealSheaf_finset_prod_ne_bot _ s (fun C _ => Blowups.Smooth.CenterComponents.Construction.smoothCenterComponentIdeal_ne_bot f I hI C)

variable [Fintype (irreducibleComponents I.subscheme)]

theorem Smooth.CenterSubunions.Construction.smoothCenterSubunionIdeal_factorization (s : Finset (irreducibleComponents I.subscheme)) :
    I = Blowups.Smooth.CenterSubunions.Construction.smoothCenterSubunionIdeal f I s * Blowups.Smooth.CenterSubunions.Construction.smoothCenterSubunionIdeal f I sᶜ := by
  classical
  rw [Blowups.Smooth.CenterSubunions.Construction.smoothCenterSubunionIdeal, Blowups.Smooth.CenterSubunions.Construction.smoothCenterSubunionIdeal, Finset.prod_mul_prod_compl,
    Blowups.Smooth.CenterComponents.Construction.smoothCenterComponentIdeal_prod]

theorem Smooth.CenterSubunions.Construction.smoothCenterSubunionIdeal_smooth (s : Finset (irreducibleComponents I.subscheme)) :
    Smooth ((Blowups.Smooth.CenterSubunions.Construction.smoothCenterSubunionIdeal f I s).subschemeι ≫ f) := by
  classical
  let K := Blowups.Smooth.CenterSubunions.Construction.smoothCenterSubunionIdeal f I s
  let L := Blowups.Smooth.CenterSubunions.Construction.smoothCenterSubunionIdeal f I sᶜ
  have he : I = L * K := (Blowups.Smooth.CenterSubunions.Construction.smoothCenterSubunionIdeal_factorization f I s).trans (mul_comm K L)
  let : Smooth ((L * K).subschemeι ≫ f) := he ▸ inferInstanceAs (Smooth (I.subschemeι ≫ f))
  exact Blowups.Smooth.ComaximalFactor.Construction.smooth_comaximal_right_factor f L K
    (Blowups.Smooth.CenterSubunions.Construction.smoothCenterSubunionIdeal_disjoint f I sᶜ s disjoint_compl_left)

def Global.CanonicalBoundaryAtlas.Construction.GlobalMixedCenterAtlas.subunion
    {β : Type} {D : β → X.IdealSheafData} (A : Global.CanonicalBoundaryAtlas.Construction.GlobalMixedCenterAtlas f I D)
    (s : Finset (irreducibleComponents I.subscheme)) :
    Global.CanonicalBoundaryAtlas.Construction.GlobalMixedCenterAtlas f (Blowups.Smooth.CenterSubunions.Construction.smoothCenterSubunionIdeal f I s) D := by
  classical
  exact A.comaximalFactor _ _ (Blowups.Smooth.CenterSubunions.Construction.smoothCenterSubunionIdeal_factorization f I s)
    (Blowups.Smooth.CenterSubunions.Construction.smoothCenterSubunionIdeal_disjoint f I s sᶜ disjoint_compl_right)

end

end OAI.AlgebraicGeometry.Resolution.Blowups

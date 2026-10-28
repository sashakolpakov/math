import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Mathlib.FieldTheory.IsAlgClosed.Basic

/-! # Integral Global Sections -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Proper.IntegralGlobalSections

noncomputable section

/-! Global functions on an integral universally closed scheme over an algebraically closed field are constants. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

variable {K : Type u} [Field K] [IsAlgClosed K] {X : Scheme.{u}}

theorem properIntegral_globalConstants_bijective (p : X ⟶ Spec (.of K))
    [IsIntegral X] [UniversallyClosed p] :
    Function.Bijective (((Scheme.ΓSpecIso (.of K)).inv ≫ p.appTop).hom) := by
  have hp : ((Scheme.ΓSpecIso (.of K)).inv ≫ p.appTop).hom.IsIntegral := by
    apply RingHom.isIntegral_respectsIso.2
      (e := (Scheme.ΓSpecIso (.of K)).symm.commRingCatIsoToRingEquiv)
    exact isIntegral_appTop_of_universallyClosed p
  exact IsAlgClosed.ringHom_bijective_of_isIntegral _ hp

theorem properIntegral_appTop_isIso (p : X ⟶ Spec (.of K))
    [IsIntegral X] [UniversallyClosed p] : IsIso p.appTop := by
  have h : IsIso ((Scheme.ΓSpecIso (.of K)).inv ≫ p.appTop) :=
    (ConcreteCategory.isIso_iff_bijective _).mpr (properIntegral_globalConstants_bijective p)
  exact (isIso_comp_left_iff (Scheme.ΓSpecIso (.of K)).inv p.appTop).mp h

def properIntegralGlobalSectionsIso (p : X ⟶ Spec (.of K))
    [IsIntegral X] [UniversallyClosed p] : CommRingCat.of K ≅ Γ(X, ⊤) := by
  letI : IsIso p.appTop := properIntegral_appTop_isIso p
  exact (Scheme.ΓSpecIso (.of K)).symm ≪≫ asIso p.appTop

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Proper.IntegralGlobalSections

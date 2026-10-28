import OAI.AlgebraicGeometry.Quotients.FiniteDescent.ShortComplexNatural
import OAI.AlgebraicGeometry.Quotients.FiniteDescent.TensorProducts
import Mathlib.CategoryTheory.Adjunction.Unique

/-! # Ring Equiv -/

namespace OAI.AlgebraicGeometry.Quotients.FiniteDescent.RingEquiv

noncomputable section

/-! Joint Cech boundary detection survives scalar extension along a ring
isomorphism, including replacement of spectral sections by the field itself. -/

set_option backward.isDefEq.respectTransparency false

open _root_.CategoryTheory _root_.CategoryTheory.Limits

universe u

namespace Construction.RingEquivCechDetection

variable {R S : Type u} [CommRing R] [CommRing S] (e : R ≃+* S)

def extendIso : ModuleCat.extendScalars e.toRingHom ≅ ModuleCat.restrictScalars e.symm.toRingHom :=
  Adjunction.leftAdjointUniq (ModuleCat.extendRestrictScalarsAdj e.toRingHom)
    (ModuleCat.restrictScalarsEquivalenceOfRingEquiv e).symm.toAdjunction

theorem jointly {C T₁ T₂ : ShortComplex (ModuleCat.{u} R)} (r₁ : C ⟶ T₁) (r₂ : C ⟶ T₂)
    (hd : CechBoundary.Construction.CechBoundaryTransport.JointlyDetects r₁ r₂) :
    CechBoundary.Construction.CechBoundaryTransport.JointlyDetects
      ((ModuleCat.extendScalars e.toRingHom).mapShortComplex.map r₁)
      ((ModuleCat.extendScalars e.toRingHom).mapShortComplex.map r₂) := by
  have hr : CechBoundary.Construction.CechBoundaryTransport.JointlyDetects
      ((ModuleCat.restrictScalars e.symm.toRingHom).mapShortComplex.map r₁)
      ((ModuleCat.restrictScalars e.symm.toRingHom).mapShortComplex.map r₂) := hd
  exact ShortComplexNatural.Construction.ShortComplexNaturalIso.jointly (extendIso e).symm r₁ r₂ hr

theorem composite {A : Type u} [CommRing A] (f : A →+* R)
    {C T₁ T₂ : ShortComplex (ModuleCat.{u} A)} (r₁ : C ⟶ T₁) (r₂ : C ⟶ T₂)
    (hd : CechBoundary.Construction.CechBoundaryTransport.JointlyDetects
      ((ModuleCat.extendScalars f).mapShortComplex.map r₁)
      ((ModuleCat.extendScalars f).mapShortComplex.map r₂)) :
    CechBoundary.Construction.CechBoundaryTransport.JointlyDetects
      ((ModuleCat.extendScalars (e.toRingHom.comp f)).mapShortComplex.map r₁)
      ((ModuleCat.extendScalars (e.toRingHom.comp f)).mapShortComplex.map r₂) := by
  have ht := jointly e ((ModuleCat.extendScalars f).mapShortComplex.map r₁)
    ((ModuleCat.extendScalars f).mapShortComplex.map r₂) hd
  exact ShortComplexNatural.Construction.ShortComplexNaturalIso.jointly (ModuleCat.extendScalarsComp f e.toRingHom).symm r₁ r₂ ht

end Construction.RingEquivCechDetection

end

end OAI.AlgebraicGeometry.Quotients.FiniteDescent.RingEquiv

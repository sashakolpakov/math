import OAI.NumberTheory.PadicHodge.PeriodInvariants.SheafCoefficients

/-! # Sheaf Coefficient Equivalence -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.SheafCoefficientEquivalence.SheafCoefficients

noncomputable section

/-! The explicit sheaf coefficient equivalence, retaining the inverse restriction functor. -/

open _root_.CategoryTheory

variable {C : Type} [Category.{0} C] (J : GrothendieckTopology C)
  {R S : Type} [CommRing R] [CommRing S] (σ : R ≃+* S)

def equivalence : Sheaf J (ModuleCat.{0} S) ≌ Sheaf J (ModuleCat.{0} R) where
  functor := sheafCompose J (ModuleCat.restrictScalars σ.toRingHom)
  inverse := sheafCompose J (ModuleCat.restrictScalars σ.symm.toRingHom)
  unitIso := NatIso.ofComponents (fun P => ObjectProperty.isoMk _
    (((ModuleCat.restrictScalarsEquivalenceOfRingEquiv σ).congrRight).unitIso.app P.obj))
  counitIso := NatIso.ofComponents (fun P => ObjectProperty.isoMk _
    (((ModuleCat.restrictScalarsEquivalenceOfRingEquiv σ).congrRight).counitIso.app P.obj))
  functor_unitIso_comp P := by
    apply ObjectProperty.hom_ext
    exact ((ModuleCat.restrictScalarsEquivalenceOfRingEquiv σ).congrRight).functor_unitIso_comp P.obj

end

end OAI.NumberTheory.PadicHodge.GeometricComparison.SheafCoefficientEquivalence.SheafCoefficients

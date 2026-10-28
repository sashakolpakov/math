import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Local.CoefficientLocalization
import Mathlib.RingTheory.FiniteType
import Mathlib.RingTheory.Adjoin.FG

/-! # Local Coefficient Ring -/

namespace OAI.AlgebraicGeometry.HilbertScheme.Presentations.Noetherian.LocalCoefficientRing

noncomputable section

/-! A finite coefficient subalgebra of a local ring has a canonical
Noetherian local enlargement mapping to the original local ring. -/

universe u v
variable {B : Type u} [CommRing B] {A : Type v} [CommRing A] [IsLocalRing A] [Algebra B A]
variable (E : Subalgebra B A)

def localCoefficientRing : Type v :=
  Localization.AtPrime (Local.CoefficientLocalization.localCoefficientPrime E.val.toRingHom)

instance localCoefficientRing_commRing : CommRing (localCoefficientRing E) :=
  inferInstanceAs (CommRing (Localization.AtPrime (Local.CoefficientLocalization.localCoefficientPrime E.val.toRingHom)))

instance localCoefficientRing_local : IsLocalRing (localCoefficientRing E) :=
  inferInstanceAs (IsLocalRing (Localization.AtPrime (Local.CoefficientLocalization.localCoefficientPrime E.val.toRingHom)))

instance localCoefficientRing_algebra : Algebra E (localCoefficientRing E) :=
  inferInstanceAs (Algebra E (Localization.AtPrime (Local.CoefficientLocalization.localCoefficientPrime E.val.toRingHom)))

instance localCoefficientRing_baseAlgebra : Algebra B (localCoefficientRing E) :=
  ((algebraMap E (localCoefficientRing E)).comp (algebraMap B E)).toAlgebra

instance localCoefficientRing_baseTower : IsScalarTower B E (localCoefficientRing E) :=
  IsScalarTower.of_algebraMap_eq (fun _ => rfl)

instance localCoefficientRing_targetAlgebra : Algebra (localCoefficientRing E) A :=
  (Local.CoefficientLocalization.localCoefficientLocalizationMap E.val.toRingHom).toAlgebra

instance localCoefficientRing_targetTower : IsScalarTower B (localCoefficientRing E) A := by
  apply IsScalarTower.of_algebraMap_eq
  intro b
  exact (RingHom.congr_fun (Local.CoefficientLocalization.localCoefficientLocalizationMap_comp E.val.toRingHom)
    (algebraMap B E b)).symm

instance localCoefficientRing_noetherian [IsNoetherianRing B] [Algebra.FiniteType B E] :
    IsNoetherianRing (localCoefficientRing E) := by
  have : IsNoetherianRing E := Algebra.FiniteType.isNoetherianRing B E
  exact IsLocalization.isNoetherianRing (Local.CoefficientLocalization.localCoefficientPrime E.val.toRingHom).primeCompl
    (Localization.AtPrime (Local.CoefficientLocalization.localCoefficientPrime E.val.toRingHom)) inferInstance

instance localCoefficientRing_baseLocalHom [IsLocalRing B] [IsLocalHom (algebraMap B A)] :
    IsLocalHom (algebraMap B (localCoefficientRing E)) := by
  have : IsLocalHom ((algebraMap (localCoefficientRing E) A).comp
      (algebraMap B (localCoefficientRing E))) := by
    rw [← IsScalarTower.algebraMap_eq B (localCoefficientRing E) A]
    infer_instance
  exact isLocalHom_of_comp (algebraMap B (localCoefficientRing E))
    (algebraMap (localCoefficientRing E) A)

end

end OAI.AlgebraicGeometry.HilbertScheme.Presentations.Noetherian.LocalCoefficientRing

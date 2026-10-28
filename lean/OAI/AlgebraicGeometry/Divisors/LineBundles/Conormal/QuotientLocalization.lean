import OAI.AlgebraicGeometry.Divisors.LineBundles.Conormal.Localization
import OAI.AlgebraicGeometry.Divisors.LineBundles.LocalizedModuleScalars
import OAI.AlgebraicGeometry.Divisors.LineBundles.QuotientLocalization

/-! # Quotient Localization -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.Conormal.QuotientLocalization.BundleCycles

noncomputable section

/-! # LineBundleCycles: actual conormal localization over the quotient coefficient rings -/

variable {R : Type} [CommRing R] (I : Ideal R) (S : Type) [CommRing S] [Algebra R S]

abbrev conormalQuotientAlgebra : Algebra (R ⧸ I) (S ⧸ I.map (algebraMap R S)) :=
  (QuotientLocalization.BundleCycles.quotientLocalizationMap S I).toAlgebra

abbrev conormalQuotientModule : Module (R ⧸ I) (I.map (algebraMap R S)).Cotangent :=
  Module.compHom (I.map (algebraMap R S)).Cotangent (QuotientLocalization.BundleCycles.quotientLocalizationMap S I)

attribute [local instance] conormalQuotientAlgebra conormalQuotientModule

instance conormalQuotientScalar_tower : IsScalarTower R (R ⧸ I) (I.map (algebraMap R S)).Cotangent :=
  IsScalarTower.of_algebraMap_smul fun r m => by
    change Ideal.Quotient.mk (I.map (algebraMap R S)) (algebraMap R S r) • m = r • m
    change algebraMap S (S ⧸ I.map (algebraMap R S)) (algebraMap R S r) • m = r • m
    rw [algebraMap_smul, algebraMap_smul]

instance conormalQuotientTarget_tower :
    IsScalarTower (R ⧸ I) (S ⧸ I.map (algebraMap R S)) (I.map (algebraMap R S)).Cotangent :=
  IsScalarTower.of_algebraMap_smul fun _ _ => rfl

def conormalQuotientLocalizationMap : I.Cotangent →ₗ[R ⧸ I] (I.map (algebraMap R S)).Cotangent :=
  (LinearMap.extendScalarsOfSurjectiveEquiv (Ideal.Quotient.mk_surjective :
    Function.Surjective (algebraMap R (R ⧸ I)))) (Localization.BundleCycles.conormalLocalizationMap I S)

theorem conormalQuotientLocalizationMap_toCotangent (a : I) :
    conormalQuotientLocalizationMap I S (I.toCotangent a) =
      (I.map (algebraMap R S)).toCotangent ⟨algebraMap R S a.val, Ideal.mem_map_of_mem _ a.property⟩ := rfl

variable (D : Submonoid R) [IsLocalization D S]

instance conormalQuotientLocalizationMap_isLocalizedModule :
    IsLocalizedModule (D.map (Ideal.Quotient.mk I)) (conormalQuotientLocalizationMap I S) := by
  have : IsLocalizedModule D ((conormalQuotientLocalizationMap I S).restrictScalars R) :=
    Localization.BundleCycles.conormalLocalizationMap_isLocalizedModule I D S
  exact LocalizedModuleScalars.BundleCycles.isLocalizedModule_of_restrictScalars D (conormalQuotientLocalizationMap I S)

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.Conormal.QuotientLocalization.BundleCycles

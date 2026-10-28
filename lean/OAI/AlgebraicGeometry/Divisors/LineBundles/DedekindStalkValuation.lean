import OAI.AlgebraicGeometry.Divisors.LineBundles.Normal.LocalValuation

/-! # Dedekind Stalk Valuation -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.DedekindStalkValuation.BundleCycles

noncomputable section

/-! Actual stalks of Dedekind spectra are valuation rings. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

theorem stalk_valuation (A : Type u) [CommRing A] [IsDedekindDomain A]
    (x : Spec (.of A)) : ValuationRing ((Spec (.of A)).presheaf.stalk x) := by
  let : x.asIdeal.IsPrime := x.isPrime
  let : Algebra A ((Spec (.of A)).presheaf.stalk x) := StructureSheaf.stalkAlgebra A x
  let : IsLocalization.AtPrime ((Spec (.of A)).presheaf.stalk x) x.asIdeal :=
    StructureSheaf.IsLocalization.to_stalk A x
  let : IsDedekindDomain ((Spec (.of A)).presheaf.stalk x) :=
    IsLocalization.AtPrime.isDedekindDomain A x.asIdeal _
  exact Normal.LocalValuation.BundleCycles.normal_local_valuation _

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.DedekindStalkValuation.BundleCycles

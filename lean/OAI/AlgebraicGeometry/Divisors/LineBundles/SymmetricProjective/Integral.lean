import OAI.AlgebraicGeometry.Divisors.LineBundles.SymmetricProjective.Noetherian
import OAI.AlgebraicGeometry.Divisors.LineBundles.SymmetricProjective.IntegralFibers

/-! # Integral -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.SymmetricProjective.Integral.BundleCycles

noncomputable section

/-! Separatedness of finite symmetric projective spectra and
integrality of finite free projective bundles over an integral affine base. -/

open _root_.AlgebraicGeometry _root_.CategoryTheory

variable (R M : Type) [CommRing R] [AddCommGroup M] [Module R M] [Module.Finite R M]

instance symmetricProjective_isSeparated : (Scheme.BundleCycles.symmetricProjectiveScheme R M).IsSeparated := ⟨by
  rw [← Limits.terminal.comp_from (Scheme.BundleCycles.symmetricProjectiveToBase R M)]
  infer_instance⟩

variable [IsNoetherianRing R] [IsDomain R] {ι : Type} [Fintype ι] [Nonempty ι]
    (b : Module.Basis ι R M)

omit [Module.Finite R M] in
include b in
theorem symmetricProjective_isIntegral_of_basis : IsIntegral (Scheme.BundleCycles.symmetricProjectiveScheme R M) := by
  let : Smooth (Scheme.BundleCycles.symmetricProjectiveToBase R M) := (Symmetric.BasisAffineChart.BundleCycles.symmetricProjective_hasAffineSpaceSourceCharts b).smooth
  let : GeometricallyIntegral (Scheme.BundleCycles.symmetricProjectiveToBase R M) := IntegralFibers.BundleCycles.symmetricProjective_geometricallyIntegral b
  exact GeometricallyIntegral.isIntegral_of_isLocallyNoetherian (Scheme.BundleCycles.symmetricProjectiveToBase R M)

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.SymmetricProjective.Integral.BundleCycles

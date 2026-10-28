import OAI.AlgebraicGeometry.Divisors.LineBundles.SymmetricProjective.Proper
import Mathlib.AlgebraicGeometry.Noetherian

/-! # Noetherian -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.SymmetricProjective.Noetherian.BundleCycles

/-! A finite symmetric projective spectrum over a Noetherian ring
is an actual Noetherian scheme. -/

open _root_.AlgebraicGeometry _root_.CategoryTheory

variable (R M : Type) [CommRing R] [IsNoetherianRing R] [AddCommGroup M] [Module R M] [Module.Finite R M]

instance symmetricProjective_isNoetherian : AlgebraicGeometry.IsNoetherian (Scheme.BundleCycles.symmetricProjectiveScheme R M) := by
  let : IsLocallyNoetherian (Scheme.BundleCycles.symmetricProjectiveScheme R M) :=
    LocallyOfFiniteType.isLocallyNoetherian (Scheme.BundleCycles.symmetricProjectiveToBase R M)
  let : CompactSpace (Scheme.BundleCycles.symmetricProjectiveScheme R M) :=
    QuasiCompact.compactSpace_of_compactSpace (Scheme.BundleCycles.symmetricProjectiveToBase R M)
  exact ⟨⟩

end OAI.AlgebraicGeometry.Divisors.LineBundles.SymmetricProjective.Noetherian.BundleCycles

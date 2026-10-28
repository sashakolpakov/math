import OAI.AlgebraicGeometry.CycleClass.Thom.Local.QuotientEulerEquiv
import OAI.AlgebraicGeometry.CycleClass.Thom.Open.StalkSupport
import OAI.AlgebraicGeometry.CycleClass.Thom.StalkPrimeQuotient

/-! # Support Euler -/

namespace OAI.AlgebraicGeometry.CycleClass.Thom.Open.SupportEuler.Constructions

noncomputable section

/-! Native local support Tor Euler sums agree with their canonical
prime quotients and are preserved by genuine open immersions. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace

open OAI.AlgebraicGeometry.CycleClass.Thom.StalkPrimeQuotient.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.StalkPrimeQuotient.Constructions.SupportScheme OAI.AlgebraicGeometry.CycleClass.Thom.Open.StalkSupport.Constructions
open OAI.AlgebraicGeometry.CycleClass.Thom.Local.QuotientEulerEquiv.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.TorAlgebra.Euler.Tor OAI.AlgebraicGeometry.CycleClass.Thom.TorAlgebra.IsolatedEuler OAI.AlgebraicGeometry.CycleClass.Thom.TorAlgebra.EulerTransport.Tor

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

def nativeSupportQuotientIso (X : Scheme) (A : IrreducibleCloseds X) (x : X) (hx : x ∈ (A : Set X)) :
    IntersectionGeometry.localSupportModule X A x hx ≅ ModuleCat.of (X.presheaf.stalk x) (StalkPrimeQuotient.Constructions.SupportScheme.quotientRing X A x hx) :=
  (StalkPrimeQuotient.Constructions.moduleEquiv X A x hx (StalkPrimeQuotient.Constructions.kernelPrime X A x hx) (StalkPrimeQuotient.Constructions.kernelPrime_image X A x hx)).toModuleIso

theorem nativeEuler_eq_quotients (X : Scheme) (A B : IrreducibleCloseds X)
    (x : X) (hxA : x ∈ (A : Set X)) (hxB : x ∈ (B : Set X)) (d : ℕ) :
    TorAlgebra.Euler.Tor.euler (X.presheaf.stalk x) (IntersectionGeometry.localSupportModule X A x hxA) (IntersectionGeometry.localSupportModule X B x hxB) d =
      TorAlgebra.Euler.Tor.euler (X.presheaf.stalk x) (ModuleCat.of _ (StalkPrimeQuotient.Constructions.SupportScheme.quotientRing X A x hxA))
        (ModuleCat.of _ (StalkPrimeQuotient.Constructions.SupportScheme.quotientRing X B x hxB)) d :=
  (TorAlgebra.IsolatedEuler.euler_iso_left _ (nativeSupportQuotientIso X A x hxA) _ d).trans
    (TorAlgebra.EulerTransport.Tor.iso_right _ _ (nativeSupportQuotientIso X B x hxB) d)

theorem open_support_euler {X Y : Scheme} (f : X ⟶ Y) [IsOpenImmersion f]
    (A B : IrreducibleCloseds X) (C D : IrreducibleCloseds Y)
    (hAC : f (IntersectionGeometry.supportPoint A) = IntersectionGeometry.supportPoint C) (hBD : f (IntersectionGeometry.supportPoint B) = IntersectionGeometry.supportPoint D)
    (x : X) (hxA : x ∈ (A : Set X)) (hxB : x ∈ (B : Set X))
    (hxC : f x ∈ (C : Set Y)) (hxD : f x ∈ (D : Set Y)) (d : ℕ) :
    TorAlgebra.Euler.Tor.euler (Y.presheaf.stalk (f x)) (ModuleCat.of _ (StalkPrimeQuotient.Constructions.SupportScheme.quotientRing Y C (f x) hxC))
      (ModuleCat.of _ (StalkPrimeQuotient.Constructions.SupportScheme.quotientRing Y D (f x) hxD)) d =
    TorAlgebra.Euler.Tor.euler (X.presheaf.stalk x) (ModuleCat.of _ (StalkPrimeQuotient.Constructions.SupportScheme.quotientRing X A x hxA))
      (ModuleCat.of _ (StalkPrimeQuotient.Constructions.SupportScheme.quotientRing X B x hxB)) d := by
  have h := Local.QuotientEulerEquiv.Constructions.euler_quotients_ringEquiv (Y.presheaf.stalk (f x)) (X.presheaf.stalk x)
    (asIso (f.stalkMap x)).commRingCatIsoToRingEquiv (StalkPrimeQuotient.Constructions.kernelPrime Y C (f x) hxC).asIdeal
      (StalkPrimeQuotient.Constructions.kernelPrime Y D (f x) hxD).asIdeal d
  exact h.trans (Local.QuotientEulerEquiv.Constructions.euler_quotients_congr _ _ _ _ _
    (StalkSupport.Constructions.kernelPrime_map f A C hAC x hxA hxC) (StalkSupport.Constructions.kernelPrime_map f B D hBD x hxB hxD) d)

end

end OAI.AlgebraicGeometry.CycleClass.Thom.Open.SupportEuler.Constructions

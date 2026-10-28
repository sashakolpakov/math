import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.PrimeFiltrationEuler
import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Tor.EulerTransport
import Mathlib.RingTheory.Regular.Category

/-! # Quotient Finite Support -/

namespace OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Regular.QuotientFiniteSupport

noncomputable section

/-! A regular scalar quotient of finite projective dimension has
zero Euler pairing against a module supported at one point. This uses
the native scalar exact sequence and does not require a domain. -/

set_option backward.isDefEq.respectTransparency false

open _root_.CategoryTheory _root_.CategoryTheory.Limits

universe u

theorem euler_zero (R : Type u) [CommRing R] [IsNoetherianRing R]
    (M N : ModuleCat.{u} R) [Module.Finite R M] [Module.Finite R N]
    (r : R) (hr : IsSMulRegular M r)
    (d : ℕ) [HasProjectiveDimensionLE (ModuleCat.of R (QuotSMulTop r M)) d]
    (p : PrimeSpectrum R) (hN : Module.support R N ⊆ {p}) :
    ProjectionFormula.Tor.Euler.euler R (.of R (QuotSMulTop r M)) N d = 0 := by
  let Q := ModuleCat.of R (QuotSMulTop r M)
  have hMfin := ProjectionFormula.Tor.FiniteLength.tor_length_ne_top R M N p (Set.inter_subset_right.trans hN)
  have hQfin := ProjectionFormula.Tor.FiniteLength.tor_length_ne_top R Q N p (Set.inter_subset_right.trans hN)
  have hv : IsZero (((Tor (ModuleCat R) (d + 1)).obj Q).obj N) :=
    IsZero.of_iso (BoundedResolution.tor_isZero R N Q d (d + 1) (by omega))
      (ProjectionFormula.Tor.Symmetry.iso R Q N (d + 1))
  have he := ProjectionFormula.Tor.Euler.additivity R N (M.smulShortComplex r) hr.smulShortComplex_shortExact d
    hMfin hMfin hQfin hv
  change ProjectionFormula.Tor.Euler.euler R M N d = ProjectionFormula.Tor.Euler.euler R M N d + ProjectionFormula.Tor.Euler.euler R Q N d at he
  linarith

end

end OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Regular.QuotientFiniteSupport

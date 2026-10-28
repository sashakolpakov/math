import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.ResolutionScalarContraction
import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.ScalarLeftInverse

/-! # Resolution Base Change Endpoints -/

namespace OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.ResolutionBaseChangeEndpoints

noncomputable section

/-! The endpoint maps of a bounded free resolution retain injectivity
after extension to a domain when an annihilating scalar stays nonzero. -/

set_option backward.isDefEq.respectTransparency false

open _root_.CategoryTheory _root_.CategoryTheory.Limits

universe u

variable (R S : Type u) [CommRing R] [CommRing S] [IsDomain S] [Algebra R S]
  (M : ModuleCat.{u} R) (P : ProjectiveResolution M) (r : R)
  (hr : ∀ x : M, r • x = 0) (hrS : algebraMap R S r ≠ 0)

include hr hrS

theorem top_injective (n : ℕ) (hn : IsZero (P.complex.X (n + 2)))
    [Module.Free R (P.complex.X (n + 1))] :
    Function.Injective ((P.complex.d (n + 1) n).hom.baseChange S) := by
  let u := (ResolutionScalarContraction.homotopy R M P r hr).hom n (n + 1)
  have he : u.hom.comp (P.complex.d (n + 1) n).hom = r • LinearMap.id :=
    ModuleCat.hom_ext_iff.mp (ResolutionScalarContraction.top_comp R M P r hr n hn)
  exact ScalarLeftInverse.injective R S _ u.hom r hrS he

theorem lift_injective [Module.Free R (P.complex.X 0)] :
    Function.Injective (((P.complex.d 1 0).hom.comp
      (ResolutionScalarContraction.lift R M P r hr).hom).baseChange S) := by
  have he : (P.complex.d 1 0).hom.comp
      (ResolutionScalarContraction.lift R M P r hr).hom = r • LinearMap.id :=
    ModuleCat.hom_ext_iff.mp (ResolutionScalarContraction.lift_comp R M P r hr)
  exact ScalarLeftInverse.scalar_injective R S _ r hrS he

end

end OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.ResolutionBaseChangeEndpoints

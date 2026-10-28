import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Finite.ProjectivePrimePrincipal
import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Smooth.StalkDimension
import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Stalk.PrimeQuotient
import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Divisor.Stalk

/-! # Local Equations -/

namespace OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Smooth.LocalEquations

noncomputable section

/-! Every divisor support on a smooth projective scheme has an actual
nonzero principal defining ideal at every point, in every dimension. -/

set_option backward.isDefEq.respectTransparency false

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace

open OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Local.Principal OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Stalk.PrimeQuotient

variable (X : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation) (m : ℕ) [SmoothOfRelativeDimension m X.structureMap]

include m

theorem stalk_factorial (x : X.carrier) :
    UniqueFactorizationMonoid (X.carrier.presheaf.stalk x) := by
  let R := X.carrier.presheaf.stalk x
  let : IsDomain R := X.stalk_isDomain x
  let : IsIntegrallyClosed R := Normal.stalk_integrallyClosed X.structureMap x
  apply UniqueFactorizationMonoid.of_forall_isPrincipal_of_height_eq_one
  intro p hp hheight
  let : HasProjectiveDimensionLE (ModuleCat.of R (R ⧸ p)) m :=
    StalkDimension.stalk_bound X.structureMap m x _
  exact Finite.ProjectivePrimePrincipal.principal R p hheight m

theorem kernel_principal (A : X.DimensionCycleSupport 1) (x : X.carrier)
    (hx : x ∈ (A.val : Set X.carrier)) :
    (RingHom.ker (Local.Principal.supportStalkMap X.carrier A.val x hx).hom).IsPrincipal := by
  let R := X.carrier.presheaf.stalk x
  let : IsDomain R := X.stalk_isDomain x
  let : UniqueFactorizationMonoid R := stalk_factorial X m x
  let p := Stalk.PrimeQuotient.kernelPrime X.carrier A.val x hx
  apply UniqueFactorizationMonoid.isPrincipal_of_height_eq_one (p := p.asIdeal)
  rw [Stalk.Localization.height_eq_coheight_image, Stalk.PrimeQuotient.kernelPrime_image]
  exact CurveSupports.coheight_one X m A

theorem exists_equation (A : X.DimensionCycleSupport 1) (x : X.carrier)
    (hx : x ∈ (A.val : Set X.carrier)) :
    ∃ r : X.carrier.presheaf.stalk x, r ≠ 0 ∧
      RingHom.ker (Local.Principal.supportStalkMap X.carrier A.val x hx).hom = Ideal.span {r} := by
  obtain ⟨r, hr⟩ := (kernel_principal X m A x hx).principal
  refine ⟨r, ?_, hr⟩
  intro hzero
  apply Divisor.Stalk.supportStalkMap_ker_ne_bot X m 1 (by decide) A x hx
  rw [hr, hzero, Submodule.span_zero_singleton]

end

end OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Smooth.LocalEquations

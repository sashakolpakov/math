import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Etale.RegularRing
import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Smooth.StalkDimension
import Mathlib.RingTheory.RegularLocalRing.Polynomial

/-! # Stalk Regular -/

namespace OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Smooth.StalkRegular

noncomputable section

/-! The actual stalks of a smooth scheme over a field are regular local
rings. The proof passes through its genuine standard smooth charts and
their etale polynomial presentations. -/

set_option backward.isDefEq.respectTransparency false

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

theorem stalk_regular {K : Type u} [Field K] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of K)) (m : ℕ) [SmoothOfRelativeDimension m f] (x : X) :
    IsRegularLocalRing (X.presheaf.stalk x) := by
  obtain ⟨U, hU, V, hV, hx, e, hstd⟩ :=
    SmoothOfRelativeDimension.exists_isStandardSmoothOfRelativeDimension (n := m) (f := f) x
  have hu : U = ⊤ := by
    ext y
    constructor
    · intro _
      trivial
    · intro _
      exact (Subsingleton.elim (f x) y) ▸ e hx
  subst U
  let := Betti.AffineDimension.Realization.sectionBaseAlgebra f V
  change Algebra.IsStandardSmoothOfRelativeDimension m Γ(Spec (.of K), ⊤) Γ(X, V) at hstd
  let := hstd
  let : IsRegularRing Γ(Spec (.of K), ⊤) := IsRegularRing.of_ringEquiv
    (Scheme.ΓSpecIso (.of K)).commRingCatIsoToRingEquiv.symm
  obtain ⟨g, hg⟩ := Algebra.IsStandardSmoothOfRelativeDimension.exists_etale_mvPolynomial
    m Γ(Spec (.of K), ⊤) Γ(X, V)
  let P := MvPolynomial (Fin m) Γ(Spec (.of K), ⊤)
  let := g.toRingHom.toAlgebra
  let : Algebra.Etale P Γ(X, V) := RingHom.etale_algebraMap.mp hg
  let : IsNoetherianRing Γ(X, V) := Algebra.FiniteType.isNoetherianRing P Γ(X, V)
  let : IsRegularRing Γ(X, V) := ProjectionFormula.Etale.RegularRing.regular P Γ(X, V)
  let := (X.presheaf.germ V x hx).hom.toAlgebra
  let T := (hV.primeIdealOf ⟨x, hx⟩).asIdeal.primeCompl
  let : IsLocalization T (X.presheaf.stalk x) := hV.isLocalization_stalk ⟨x, hx⟩
  exact ProjectionFormula.Etale.RegularRing.local_localization Γ(X, V) (X.presheaf.stalk x) T

theorem maximalIdeal_generators {K : Type u} [Field K] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of K)) (m : ℕ) [SmoothOfRelativeDimension m f] (x : X) :
    ((IsLocalRing.maximalIdeal (X.presheaf.stalk x)).spanFinrank : WithBot ℕ∞) =
      Order.coheight x := by
  let := stalk_regular f m x
  exact ((isRegularLocalRing_iff (X.presheaf.stalk x)).mp inferInstance).trans
    (ringKrullDim_stalk_eq_coheight x)

end

end OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Smooth.StalkRegular

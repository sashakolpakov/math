import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Tor.DimensionBound
import OAI.AlgebraicGeometry.Betti.AffineDimension
import Mathlib.RingTheory.RingHom.StandardSmooth
import Mathlib.AlgebraicGeometry.Morphisms.Smooth

/-! # Stalk Dimension -/

namespace OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Smooth.StalkDimension

noncomputable section

/-! The local ring of a scheme smooth of relative dimension m over a field
has projective dimension at most m for every module. Standard smooth charts
factor through an etale algebra over a polynomial ring in exactly m variables. -/

set_option backward.isDefEq.respectTransparency false

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

open OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Polynomial.DimensionBound

theorem stalk_bound {K : Type u} [Field K] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of K)) (m : ℕ) [SmoothOfRelativeDimension m f] (x : X) :
    Polynomial.DimensionBound.GlobalBound (X.presheaf.stalk x) m := by
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
  have hb : Polynomial.DimensionBound.GlobalBound Γ(Spec (.of K), ⊤) 0 :=
    Polynomial.DimensionBound.bound_of_ringEquiv (Scheme.ΓSpecIso (.of K)).commRingCatIsoToRingEquiv.symm 0 (Polynomial.DimensionBound.field_bound K)
  obtain ⟨g, hg⟩ := Algebra.IsStandardSmoothOfRelativeDimension.exists_etale_mvPolynomial
    m Γ(Spec (.of K), ⊤) Γ(X, V)
  let := g.toRingHom.toAlgebra
  let : Algebra.Etale (MvPolynomial (Fin m) Γ(Spec (.of K), ⊤)) Γ(X, V) :=
    RingHom.etale_algebraMap.mp hg
  have hVbound : Polynomial.DimensionBound.GlobalBound Γ(X, V) m :=
    ProjectionFormula.Etale.DimensionBound.extension_bound (MvPolynomial (Fin m) Γ(Spec (.of K), ⊤)) Γ(X, V)
      m (Polynomial.DimensionBound.mvPolynomial_bound_of_zero Γ(Spec (.of K), ⊤) hb m)
  let := (X.presheaf.germ V x hx).hom.toAlgebra
  let T := (hV.primeIdealOf ⟨x, hx⟩).asIdeal.primeCompl
  let : IsLocalization T (X.presheaf.stalk x) := hV.isLocalization_stalk ⟨x, hx⟩
  let : Module.Flat Γ(X, V) (X.presheaf.stalk x) := IsLocalization.flat _ T
  let : Algebra.FormallyUnramified Γ(X, V) (X.presheaf.stalk x) :=
    Algebra.FormallyUnramified.of_isLocalization T
  let : Algebra.EssFiniteType Γ(X, V) (X.presheaf.stalk x) :=
    Algebra.EssFiniteType.of_isLocalization _ T
  exact ProjectionFormula.Etale.DimensionBound.extension_bound Γ(X, V) (X.presheaf.stalk x) m hVbound

theorem stalk_tor_length_zero {K : Type u} [Field K] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of K)) (m : ℕ) [SmoothOfRelativeDimension m f] (x : X)
    (M N : ModuleCat.{u} (X.presheaf.stalk x)) (i : ℕ) (hi : m < i) :
    Module.length (X.presheaf.stalk x)
      (((Tor (ModuleCat (X.presheaf.stalk x)) i).obj M).obj N) = 0 :=
  ProjectionFormula.Tor.DimensionBound.tor_length_zero_of_bound _ m (stalk_bound f m x) M N i hi

end

end OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Smooth.StalkDimension

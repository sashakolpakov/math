import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.PolarizationIsogeny
import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.PolarizationType
import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.PositiveFormula
import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.PELAction

/-! # Polarization Assembly -/

namespace OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.PolarizationAssembly.Construction

noncomputable section

/-!
The field-to-family construction produces the quotient polarization:
finite flat isogeny, scheme-theoretic degree, geometric elementary divisors,
and the normalized ample Poincare formula. Relative dual data and its maps
are still supplied explicitly; no relative polarization is an input.
-/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj

universe u

/-- Retain all isogeny geometry when forgetting the fixed dimension.
Finite presentation follows from the smooth abelian structure maps. -/
def isogenyForgetDimension
    {S : Scheme.{u}} {g : ℕ} {A B : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g S}
    (f : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme.Isogeny A B) :
    Picard.PoincareBundle.Epi.Construction.AbelianScheme.Isogeny (PELAction.Construction.abelianSchemeForgetDimension A)
      (PELAction.Construction.abelianSchemeForgetDimension B) := by
  have : LocallyOfFinitePresentation (f.hom.left ≫ B.scheme.hom) := by
    rw [f.hom.w]
    infer_instance
  exact {
    hom := f.hom
    isMonHom := f.preservesGroup
    finite := f.finite
    flat := f.flat
    surjective := f.surjective
    finitePresentation :=
      ArithmeticGeometry.OrdinaryLocus.Openness.FinitePresentation.Construction.locallyOfFinitePresentation_of_comp_of_locallyOfFiniteType
        f.hom.left B.scheme.hom }

theorem isogeny_eq_of_hom_eq
    {S : Scheme.{u}} {g h : ℕ} {A : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g S} {B : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme h S}
    {p q : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme.Isogeny A B} (hpq : p.hom = q.hom) : p = q := by
  cases p
  cases q
  cases hpq
  rfl

theorem polarization_eq_of_hom_eq
    {S : Scheme.{u}} {g : ℕ} {A : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g S} {D : AbelianModuli.HilbertConstruction.Dual.Data.DualAbelianData A}
    {δ : Fin g → ℕ} {p q : AbelianModuli.HilbertConstruction.PolarizationData.Polarization D δ} (hpq : p.isogeny.hom = q.isogeny.hom) :
    p = q := by
  cases p with
  | mk pi pk pp =>
    cases q with
    | mk qi qk qp =>
      have h : pi = qi := isogeny_eq_of_hom_eq hpq
      cases h
      rfl

set_option backward.isDefEq.respectTransparency false in
/-- The actual field polarizations of the same type construct a unique
relative HilbertConstruction polarization. In particular, its type and positivity are
proved from PoincareBundle on geometric fibers, rather than assumed for the family. -/
theorem relative_polarization_from_field_polarizations
    {K : Type u} [Field K] [CharZero K] {S : Scheme.{u}}
    (base : S ⟶ Spec (.of K)) {dim : ℕ}
    (A B : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme dim S) (DA : AbelianModuli.HilbertConstruction.Dual.Data.DualAbelianData A) (DB : AbelianModuli.HilbertConstruction.Dual.Data.DualAbelianData B)
    (δ : Fin dim → ℕ) (polarization : AbelianModuli.HilbertConstruction.PolarizationData.Polarization DA δ)
    (n : ℕ) (hn : 0 < n) (f : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme.Isogeny A B)
    (g : B.scheme ⟶ A.scheme) [IsMonHom g]
    (fd : DB.abelian.scheme ⟶ DA.abelian.scheme) [IsMonHom fd]
    (gd : DA.abelian.scheme ⟶ DB.abelian.scheme) [IsMonHom gd]
    (hfg : f.hom ≫ g = (𝟙 A.scheme) ^ n)
    (hfdgd : fd ≫ gd = (𝟙 DB.abelian.scheme) ^ n)
    (hgdfd : gd ≫ fd = (𝟙 DA.abelian.scheme) ^ n)
    (h_TorsionQuotient : Unit.Construction.TorsionQuotientInput.{u})
    (h_PoincareBundle : ∀ (L : Type u) [Field L] [IsAlgClosed L] (s : Spec (.of L) ⟶ S),
      ∃ p : AbelianModuli.HilbertConstruction.PolarizationData.Polarization (DB.pullback s) δ,
        (Over.pullback s).map f.hom ≫ p.isogeny.hom ≫ (Over.pullback s).map fd =
          ((Over.pullback s).map polarization.isogeny.hom) ^ n) :
    ∃! p : AbelianModuli.HilbertConstruction.PolarizationData.Polarization DB δ,
      f.hom ≫ p.isogeny.hom ≫ fd = polarization.isogeny.hom ^ n := by
  obtain ⟨p0, hp0, huniq, hmatch⟩ := PolarizationIsogeny.Construction.relative_polarization_isogeny_from_field_morphisms
    base (PELAction.Construction.abelianSchemeForgetDimension A) (PELAction.Construction.abelianSchemeForgetDimension B)
    (PELAction.Construction.abelianSchemeForgetDimension DA.abelian) (PELAction.Construction.abelianSchemeForgetDimension DB.abelian)
    n hn (isogenyForgetDimension f) g fd gd polarization.isogeny.hom hfg hfdgd hgdfd h_TorsionQuotient
    (fun L _ _ s => by
      obtain ⟨r, hr⟩ := h_PoincareBundle L s
      exact ⟨r.isogeny.hom, r.isogeny.preservesGroup, r.isogeny.finite,
        r.isogeny.flat, r.isogeny.surjective, hr⟩)
  let p : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme.Isogeny B DB.abelian := {
    hom := p0.hom
    preservesGroup := p0.isMonHom
    finite := p0.finite
    flat := p0.flat
    surjective := p0.surjective }
  have htype : p.HasPolarizationType δ := by
    apply PolarizationType.Construction.polarization_type_of_geometric_baseChanges p δ
    intro L _ _ s
    obtain ⟨r, hr⟩ := h_PoincareBundle L s
    have he : (p.pullback s).hom = r.isogeny.hom :=
      hmatch L s r.isogeny.hom r.isogeny.preservesGroup hr
    exact (isogeny_eq_of_hom_eq he).symm ▸ r.kernelType
  have hpositive : ∀ (L : Type u) [Field L] [IsAlgClosed L] (s : Spec (.of L) ⟶ S),
      AbelianModuli.HilbertConstruction.PolarizationData.PositiveOnGeometricFiber DB p.hom L s := by
    intro L _ _ s
    obtain ⟨r, hr⟩ := h_PoincareBundle L s
    have he : (Over.pullback s).map p.hom = r.isogeny.hom :=
      hmatch L s r.isogeny.hom r.isogeny.preservesGroup hr
    have hpos : AbelianModuli.HilbertConstruction.PolarizationData.PositiveOnGeometricFiber (DB.pullback s)
        ((Over.pullback s).map p.hom) L (𝟙 _) := by
      rw [he]
      exact r.positive L (𝟙 _)
    have h := (PositiveFormula.Construction.positiveOnGeometricFiber_pullback_iff DB p.hom s L (𝟙 _)).mp hpos
    simpa only [Category.id_comp] using h
  refine ⟨⟨p, htype, hpositive⟩, hp0, ?_⟩
  intro r hr
  exact polarization_eq_of_hom_eq
    (huniq r.isogeny.hom r.isogeny.preservesGroup hr)

end

end OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.PolarizationAssembly.Construction

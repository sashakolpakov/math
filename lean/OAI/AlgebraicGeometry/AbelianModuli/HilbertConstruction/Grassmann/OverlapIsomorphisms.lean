import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Grassmann.OverlapEquivalence

/-! # Overlap Isomorphisms -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Grassmann.OverlapIsomorphisms

noncomputable section

/-! Isomorphisms of the actual principal open Grassmannian overlap schemes. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

variable (R : Type u) [CommRing R] {k l : ℕ} (τ : Equiv.Perm (Fin k ⊕ Fin l))

/-- The natural frame transition identifies the two localized coordinate algebras. -/
def grassmannOverlapAlgebraIso :
    OverlapSchemes.grassmannOverlapCoordinateAlgebra R τ ≅ OverlapSchemes.grassmannOverlapCoordinateAlgebra R τ.symm :=
  (OverlapFunctor.grassmannOverlapCorepresentable R τ).uniqueUpToIso
    ((OverlapFunctor.grassmannOverlapCorepresentable R τ.symm).ofIso (OverlapEquivalence.grassmannOverlapFunctorIso R τ).symm)

/-- The induced algebra map acts on the universal point by the prescribed change of frame. -/
theorem grassmannOverlapAlgebraIso_universal :
    (OverlapFunctor.grassmannOverlapCorepresentable R τ.symm).homEquiv (grassmannOverlapAlgebraIso R τ).inv =
      OverlapEquivalence.grassmannOverlapPointEquiv τ ((OverlapFunctor.grassmannOverlapCorepresentable R τ).homEquiv (𝟙 _)) := by
  change (OverlapFunctor.grassmannOverlapCorepresentable R τ.symm).homEquiv
    ((OverlapFunctor.grassmannOverlapCorepresentable R τ.symm).homEquiv.symm _) = _
  exact (OverlapFunctor.grassmannOverlapCorepresentable R τ.symm).homEquiv.apply_symm_apply _

/-- On every coefficient algebra the induced map is exactly the frame transition. -/
theorem grassmannOverlapAlgebraIso_comp {A : CommAlgCat.{u} R}
    (f : OverlapSchemes.grassmannOverlapCoordinateAlgebra R τ ⟶ A) :
    (OverlapFunctor.grassmannOverlapCorepresentable R τ.symm).homEquiv ((grassmannOverlapAlgebraIso R τ).inv ≫ f) =
      OverlapEquivalence.grassmannOverlapPointEquiv τ ((OverlapFunctor.grassmannOverlapCorepresentable R τ).homEquiv f) := by
  rw [Functor.CorepresentableBy.homEquiv_comp, grassmannOverlapAlgebraIso_universal]
  rw [(OverlapFunctor.grassmannOverlapCorepresentable R τ).homEquiv_eq f]
  exact ((OverlapEquivalence.grassmannOverlapFunctorIso R τ).hom.naturality_apply f _).symm

/-- The two principal open subschemes are isomorphic over the base ring. -/
def grassmannOverlapSchemeIso : OverlapSchemes.grassmannOverlapScheme R τ ≅ OverlapSchemes.grassmannOverlapScheme R τ.symm :=
  (algSpec (CommRingCat.of R)).mapIso (grassmannOverlapAlgebraIso R τ).symm.op

/-- Inclusion in the alternate affine chart is an actual open immersion. -/
def grassmannOverlapAlternateι : OverlapSchemes.grassmannOverlapScheme R τ ⟶ AffineCharts.grassmannAffineChart R k l :=
  (grassmannOverlapSchemeIso R τ).hom ≫ OverlapSchemes.grassmannOverlapι R τ.symm

instance grassmannOverlapAlternateι_isOpenImmersion :
    IsOpenImmersion (grassmannOverlapAlternateι R τ).left := by
  have : IsIso (grassmannOverlapSchemeIso R τ).hom.left :=
    inferInstanceAs (IsIso ((Over.forget _).map (grassmannOverlapSchemeIso R τ).hom))
  exact IsOpenImmersion.comp _ _

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Grassmann.OverlapIsomorphisms

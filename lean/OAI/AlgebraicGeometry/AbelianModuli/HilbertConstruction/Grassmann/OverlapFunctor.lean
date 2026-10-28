import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Grassmann.OverlapSchemes
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Grassmann.PermutationTransitions

/-! # Overlap Functor -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Grassmann.OverlapFunctor

noncomputable section

/-! The represented overlap functor, with its natural inclusion in the quotient-chart functor. -/

open _root_.CategoryTheory

universe u

variable (R : Type u) [CommRing R] {k l : ℕ} (τ : Equiv.Perm (Fin k ⊕ Fin l))

/-- Points of the overlap form a functor under scalar extension of their defining quotients. -/
def grassmannOverlapFunctor : CommAlgCat.{u} R ⥤ Type u where
  obj A := LocalizationChartParameters.GrassmannOverlapPoint τ A
  map f := TypeCat.ofHom (fun c => ⟨Charts.GrassmannChart.map f.hom.toRingHom c.val,
    Charts.GrassmannChart.overlap_map f.hom.toRingHom c.val τ c.property⟩)
  map_id A := by
    apply ConcreteCategory.hom_ext
    intro c
    exact Subtype.ext (Charts.GrassmannChart.map_id c.val)
  map_comp f g := by
    apply ConcreteCategory.hom_ext
    intro c
    exact Subtype.ext (Charts.GrassmannChart.map_comp f.hom.toRingHom g.hom.toRingHom c.val)

/-- The overlap condition is forgotten naturally. -/
def grassmannOverlapForget : grassmannOverlapFunctor R τ ⟶ ChartRepresentability.grassmannChartFunctor R k l where
  app _ := TypeCat.ofHom Subtype.val
  naturality _ _ _ := rfl

/-- The overlap functor is corepresented by the localized polynomial coordinate algebra. -/
def grassmannOverlapCorepresentable :
    (grassmannOverlapFunctor R τ).CorepresentableBy (OverlapSchemes.grassmannOverlapCoordinateAlgebra R τ) where
  homEquiv :=
    { toFun := fun f => LocalizationChartParameters.grassmannOverlapAlgHomEquiv R τ _ f.hom
      invFun := fun c => CommAlgCat.ofHom ((LocalizationChartParameters.grassmannOverlapAlgHomEquiv R τ _).symm c)
      left_inv := fun f => by
        apply CommAlgCat.hom_ext
        exact (LocalizationChartParameters.grassmannOverlapAlgHomEquiv R τ _).symm_apply_apply f.hom
      right_inv := fun c => (LocalizationChartParameters.grassmannOverlapAlgHomEquiv R τ _).apply_symm_apply c }
  homEquiv_comp g f := by
    apply Subtype.ext
    exact Charts.GrassmannChart.polynomialEquiv_naturality g.hom
      (f.hom.comp (Algebra.algHom R (MvPolynomial (Fin k × Fin l) R)
        (Localization.Away (Chart.OverlapDeterminants.chartOverlapPolynomial R τ))))

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Grassmann.OverlapFunctor

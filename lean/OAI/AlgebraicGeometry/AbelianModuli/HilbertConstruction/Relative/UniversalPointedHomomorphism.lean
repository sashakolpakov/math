import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Relative.UniversalPointedFieldDetection
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.MonoidalProductComparisonUnit
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.PointedMultiplicationUnit
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Abelian.SchemeProducts
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Projective.Products
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Smooth.PointedMorphisms

/-! # Universal Pointed Homomorphism -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Relative.UniversalPointedHomomorphism

noncomputable section

/-! Every pointed map between arbitrary base changes of fixed projectively presented Noetherian abelian families is a group homomorphism. The group-law equations are compared by the universal pointed-map field detector. -/
open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.CategoryTheory.MonoidalCategory
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj
universe u

theorem relativeUniversalPointedMap_isMonHom
    {S : Scheme.{u}} [IsNoetherian S] {g h : ℕ}
    (A : Abelian.Schemes.AbelianScheme g S) (B : Abelian.Schemes.AbelianScheme h S)
    (PA : Projective.ProjectivePresentations.ProjectivePresentation A.scheme) (PB : Projective.ProjectivePresentations.ProjectivePresentation B.scheme)
    (T : Over S) (f : (A.pullback T.hom).scheme ⟶ (B.pullback T.hom).scheme)
    (hf : η[(A.pullback T.hom).scheme] ≫ f = η[(B.pullback T.hom).scheme]) : IsMonHom f := by
  refine ⟨hf, ?_⟩
  let F := Over.pullback T.hom
  let C := (A.pullback T.hom).scheme
  let D := (B.pullback T.hom).scheme
  let e := Functor.Monoidal.μIso F A.scheme A.scheme
  let a : ((A.product A).pullback T.hom).scheme ⟶ D := e.inv ≫ μ[C] ≫ f
  let b : ((A.product A).pullback T.hom).scheme ⟶ D := e.inv ≫ (f ⊗ₘ f) ≫ μ[D]
  obtain ⟨h₁, h₂⟩ := PointedMultiplicationUnit.pointedMultiplicationComposites_preserve_unit f hf
  have he := MonoidalProductComparisonUnit.monoidalProductComparison_inv_preserves_unit F A.scheme A.scheme
  have ha : η[((A.product A).pullback T.hom).scheme] ≫ a = η[D] := by
    change η[F.obj (A.scheme ⊗ A.scheme)] ≫ (e.inv ≫ (μ[C] ≫ f)) = η[D]
    rw [← Category.assoc, he]
    exact h₁
  have hb : η[((A.product A).pullback T.hom).scheme] ≫ b = η[D] := by
    change η[F.obj (A.scheme ⊗ A.scheme)] ≫ (e.inv ≫ ((f ⊗ₘ f) ≫ μ[D])) = η[D]
    rw [← Category.assoc, he]
    exact h₂
  have hab : a = b := by
    let Q := (PA.product PA).product PB
    refine @UniversalPointedFieldDetection.relativeUniversalPointedMap_eq_of_fieldPullbacks S _ (g + g) h Q.dimension
      (A.product A) B Q.embedding Q.closedImmersion T a b ha hb ?_
    intro K _ s
    have hs : η[((A.pullback T.hom).pullback s).scheme] ≫ (Over.pullback s).map f =
        η[((B.pullback T.hom).pullback s).scheme] :=
      (MappedMonoidHomEquations.mappedMonoidHom_one_iff (Over.pullback s) f).mpr (congrArg (Over.pullback s).map hf)
    have hm : IsMonHom ((Over.pullback s).map f) :=
      Smooth.PointedMorphisms.abelianPointedMorphism_isMonHom ((A.pullback T.hom).pullback s)
        ((B.pullback T.hom).pullback s) ((Over.pullback s).map f) hs
    have hmul := (MappedMonoidHomEquations.mappedMonoidHom_mul_iff (Over.pullback s) f).mp hm.mul_hom
    change (Over.pullback s).map (e.inv ≫ (μ[C] ≫ f)) =
      (Over.pullback s).map (e.inv ≫ ((f ⊗ₘ f) ≫ μ[D]))
    rw [Functor.map_comp, Functor.map_comp]
    exact congrArg (fun k => (Over.pullback s).map e.inv ≫ k) hmul
  exact (cancel_epi e.inv).mp hab

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Relative.UniversalPointedHomomorphism

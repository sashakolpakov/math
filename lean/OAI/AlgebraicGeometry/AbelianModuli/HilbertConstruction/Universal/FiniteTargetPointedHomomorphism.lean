import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Universal.FiniteTargetFieldDetection
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.MonoidalProductComparisonUnit
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.PointedMultiplicationUnit
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Abelian.SchemeProducts
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Smooth.PointedMorphisms

/-! # Finite Target Pointed Homomorphism -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Universal.FiniteTargetPointedHomomorphism

noncomputable section

/-! A pointed map from a test of a fixed Noetherian projective abelian
family to an abelian family finite over another such test preserves the
group law. The target need not itself descend to the original base. -/
open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj
universe u
variable {S : Scheme.{u}} [IsNoetherian S] {g h k : ℕ}
variable (A : Abelian.Schemes.AbelianScheme g S) (B : Abelian.Schemes.AbelianScheme h S)
variable (PA : Projective.ProjectivePresentations.ProjectivePresentation A.scheme) (PB : Projective.ProjectivePresentations.ProjectivePresentation B.scheme)
variable (T : Over S) (D : Abelian.Schemes.AbelianScheme k T.left)
variable (r : D.scheme ⟶ (B.pullback T.hom).scheme) [IsMonHom r] [IsFinite r.left]

include PA PB r in
theorem universalFiniteTarget_pointedMap_isMonHom
    (f : (A.pullback T.hom).scheme ⟶ D.scheme)
    (hf : η[(A.pullback T.hom).scheme] ≫ f = η[D.scheme]) : IsMonHom f := by
  refine ⟨hf, ?_⟩
  let F := Over.pullback T.hom
  let C := (A.pullback T.hom).scheme
  let e := Functor.Monoidal.μIso F A.scheme A.scheme
  let a : ((A.product A).pullback T.hom).scheme ⟶ D.scheme := e.inv ≫ μ[C] ≫ f
  let b : ((A.product A).pullback T.hom).scheme ⟶ D.scheme := e.inv ≫ (f ⊗ₘ f) ≫ μ[D.scheme]
  obtain ⟨h₁, h₂⟩ := PointedMultiplicationUnit.pointedMultiplicationComposites_preserve_unit f hf
  have he := MonoidalProductComparisonUnit.monoidalProductComparison_inv_preserves_unit F A.scheme A.scheme
  have ha : η[((A.product A).pullback T.hom).scheme] ≫ a = η[D.scheme] := by
    change η[F.obj (A.scheme ⊗ A.scheme)] ≫ (e.inv ≫ (μ[C] ≫ f)) = _
    rw [← Category.assoc, he]
    exact h₁
  have hb : η[((A.product A).pullback T.hom).scheme] ≫ b = η[D.scheme] := by
    change η[F.obj (A.scheme ⊗ A.scheme)] ≫ (e.inv ≫ ((f ⊗ₘ f) ≫ μ[D.scheme])) = _
    rw [← Category.assoc, he]
    exact h₂
  have hab : a = b := by
    refine FiniteTargetFieldDetection.universalFiniteTarget_pointedMap_eq_of_fieldPullbacks (A.product A) B
      (PA.product PA) PB T D.scheme r a b ha hb ?_
    intro K _ s
    have hs : η[((A.pullback T.hom).pullback s).scheme] ≫ (Over.pullback s).map f =
        η[(D.pullback s).scheme] :=
      (MappedMonoidHomEquations.mappedMonoidHom_one_iff (Over.pullback s) f).mpr (congrArg (Over.pullback s).map hf)
    have hm : IsMonHom ((Over.pullback s).map f) :=
      Smooth.PointedMorphisms.abelianPointedMorphism_isMonHom ((A.pullback T.hom).pullback s) (D.pullback s)
        ((Over.pullback s).map f) hs
    have hmul := (MappedMonoidHomEquations.mappedMonoidHom_mul_iff (Over.pullback s) f).mp hm.mul_hom
    change (Over.pullback s).map (e.inv ≫ (μ[C] ≫ f)) =
      (Over.pullback s).map (e.inv ≫ ((f ⊗ₘ f) ≫ μ[D.scheme]))
    rw [Functor.map_comp, Functor.map_comp]
    exact congrArg (fun v => (Over.pullback s).map e.inv ≫ v) hmul
  exact (cancel_epi e.inv).mp hab

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Universal.FiniteTargetPointedHomomorphism

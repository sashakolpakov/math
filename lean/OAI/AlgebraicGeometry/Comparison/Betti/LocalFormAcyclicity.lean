import OAI.AlgebraicGeometry.Comparison.Betti.Algebraic.FormRestriction
import OAI.AlgebraicGeometry.Comparison.Betti.Affine.ExteriorAcyclicity
import OAI.AlgebraicGeometry.Comparison.Betti.StandardSmoothBasis

/-! # Local Form Acyclicity -/

namespace OAI.AlgebraicGeometry.Comparison.Betti.LocalFormAcyclicity

noncomputable section

/-! A basis of actual acyclic restrictions for every original algebraic form sheaf. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace

variable {X Y : Over Foundations.Scheme.ProjectiveSpace.complexBase} (f : X ⟶ Y) [IsOpenImmersion f.left]

def additiveZariskiOpenRestriction :
    Sheaf (Opens.grothendieckTopology Y.left) AddCommGrpCat.{0} ⥤
      Sheaf (Opens.grothendieckTopology X.left) AddCommGrpCat.{0} := by
  have := f.left.isOpenEmbedding.functor_isContinuous
  exact f.left.isOpenEmbedding.functor.sheafPushforwardContinuous AddCommGrpCat.{0}
    (Opens.grothendieckTopology X.left) (Opens.grothendieckTopology Y.left)

def algebraicFormAdditiveOpenRestrictionIso (n : ℕ) :
    (additiveZariskiOpenRestriction f).obj (Affine.ExteriorAcyclicity.algebraicFormAdditiveSheaf Y n) ≅
      Affine.ExteriorAcyclicity.algebraicFormAdditiveSheaf X n :=
  (sheafCompose (Opens.grothendieckTopology X.left)
    (forget₂ (ModuleCat.{0} ℂ) AddCommGrpCat.{0})).mapIso (Algebraic.FormRestriction.algebraicFormOpenRestrictionIso f n)

theorem standardSmooth_restrictedAlgebraicForms_acyclic [IsAffine X.left]
    [Algebra.IsStandardSmooth ℂ (Affine.ExteriorRestrictions.globalCoordinateAlgebra X)] (n q : ℕ) :
    Subsingleton (Sheaf.H ((additiveZariskiOpenRestriction f).obj
      (Affine.ExteriorAcyclicity.algebraicFormAdditiveSheaf Y n)) (q + 1)) := by
  let H := Sheaf.functorH (Opens.grothendieckTopology X.left) (q + 1)
  have : Subsingleton (H.obj (Affine.ExteriorAcyclicity.algebraicFormAdditiveSheaf X n)) :=
    Affine.ExteriorAcyclicity.standardSmooth_algebraicForms_acyclic X n q
  let e := H.mapIso (algebraicFormAdditiveOpenRestrictionIso f n)
  exact (ConcreteCategory.bijective_of_isIso e.hom).injective.subsingleton

theorem exists_acyclic_algebraicFormRestriction (X : Over Foundations.Scheme.ProjectiveSpace.complexBase) [Smooth X.hom]
    (W : X.left.Opens) (x : W) :
    ∃ (U : X.left.Opens), U ≤ W ∧ (x : X.left) ∈ U ∧
      ∀ (n q : ℕ), Subsingleton (Sheaf.H
        ((additiveZariskiOpenRestriction (Open.AffineIsoEvaluation.openInclusion X U)).obj
          (Affine.ExteriorAcyclicity.algebraicFormAdditiveSheaf X n)) (q + 1)) := by
  obtain ⟨U, hUW, hxU, hU, hstd⟩ := StandardSmoothBasis.exists_standardSmooth_openOver_le X W x
  have : IsAffine (Open.AffineIsoEvaluation.openOver X U).left := hU
  have : Algebra.IsStandardSmooth ℂ (Affine.ExteriorRestrictions.globalCoordinateAlgebra (Open.AffineIsoEvaluation.openOver X U)) := hstd
  exact ⟨U, hUW, hxU, fun n q =>
    standardSmooth_restrictedAlgebraicForms_acyclic (Open.AffineIsoEvaluation.openInclusion X U) n q⟩

end

end OAI.AlgebraicGeometry.Comparison.Betti.LocalFormAcyclicity

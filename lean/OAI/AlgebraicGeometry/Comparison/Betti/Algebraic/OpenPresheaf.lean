import OAI.AlgebraicGeometry.Comparison.Betti.OpenForms
import OAI.AlgebraicGeometry.Comparison.Betti.Open.Image

/-! # Open Presheaf -/

namespace OAI.AlgebraicGeometry.Comparison.Betti.Algebraic.OpenPresheaf

noncomputable section

/-! The original integer algebraic presheaf complex restricts isomorphically across an open immersion. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace Opposite

variable {X Y : Over Foundations.Scheme.ProjectiveSpace.complexBase} (f : X ⟶ Y) [IsOpenImmersion f.left]

abbrev zariskiOpenPresheafRestriction : Sheaf.CochainPullback.ComplexPresheaves Y ⥤ Sheaf.CochainPullback.ComplexPresheaves X :=
  Open.Image.openPresheafRestriction f.left.base f.left.isOpenEmbedding

instance zariskiOpenPresheafRestrictionAdditive : (zariskiOpenPresheafRestriction f).Additive where
  map_add := by intros; rfl

def zariskiOpenPresheafAdjunction : zariskiOpenPresheafRestriction f ⊣ Sheaf.CochainPullback.directImagePresheaf f :=
  Open.Image.openPresheafAdjunction f.left.base f.left.isOpenEmbedding

def zariskiOpenPresheafComplexAdjunction :
    (zariskiOpenPresheafRestriction f).mapHomologicalComplex (ComplexShape.up ℤ) ⊣
      (Sheaf.CochainPullback.directImagePresheaf f).mapHomologicalComplex (ComplexShape.up ℤ) :=
  Complex.Adjunction.onComplexes (zariskiOpenPresheafAdjunction f) (ComplexShape.up ℤ)

def restrictedAlgebraicPresheafPullbackInt :
    ((zariskiOpenPresheafRestriction f).mapHomologicalComplex (ComplexShape.up ℤ)).obj
        (Sheaves.deRhamPresheafComplexInt Y) ⟶ Sheaves.deRhamPresheafComplexInt X :=
  ((zariskiOpenPresheafComplexAdjunction f).homEquiv (Sheaves.deRhamPresheafComplexInt Y)
    (Sheaves.deRhamPresheafComplexInt X)).symm (OpenForms.presheafComplexPullbackInt f)

theorem restrictedAlgebraicDirectMapInt_isIso :
    IsIso (((zariskiOpenPresheafRestriction f).mapHomologicalComplex (ComplexShape.up ℤ)).map
      (OpenForms.presheafComplexPullbackInt f)) := by
  have (n : ℤ) : IsIso
      ((((zariskiOpenPresheafRestriction f).mapHomologicalComplex (ComplexShape.up ℤ)).map
        (OpenForms.presheafComplexPullbackInt f)).f n) := by
    have (U : X.left.Opensᵒᵖ) : IsIso
        (((((zariskiOpenPresheafRestriction f).mapHomologicalComplex (ComplexShape.up ℤ)).map
          (OpenForms.presheafComplexPullbackInt f)).f n).app U) := by
      have : IsIso ((OpenForms.deRhamPresheafPullbackInt f).app (op (f.left ''ᵁ U.unop))) :=
        OpenForms.deRhamPresheafPullbackInt_isIso_of_openImmersion f (op (f.left ''ᵁ U.unop))
          (Set.image_subset_range _ _)
      change IsIso (((OpenForms.deRhamPresheafPullbackInt f).app (op (f.left ''ᵁ U.unop))).f n)
      infer_instance
    exact NatIso.isIso_of_isIso_app _
  exact HomologicalComplex.Hom.isIso_of_components _

theorem restrictedAlgebraicPresheafPullbackInt_isIso : IsIso (restrictedAlgebraicPresheafPullbackInt f) := by
  have : IsIso (((zariskiOpenPresheafRestriction f).mapHomologicalComplex (ComplexShape.up ℤ)).map
      (OpenForms.presheafComplexPullbackInt f)) := restrictedAlgebraicDirectMapInt_isIso f
  have : IsIso ((zariskiOpenPresheafComplexAdjunction f).counit.app (Sheaves.deRhamPresheafComplexInt X)) :=
    Open.Image.openPresheafComplexCounit_isIso f.left.base f.left.isOpenEmbedding (Sheaves.deRhamPresheafComplexInt X)
  unfold restrictedAlgebraicPresheafPullbackInt
  rw [Adjunction.homEquiv_counit]
  infer_instance

end

end OAI.AlgebraicGeometry.Comparison.Betti.Algebraic.OpenPresheaf

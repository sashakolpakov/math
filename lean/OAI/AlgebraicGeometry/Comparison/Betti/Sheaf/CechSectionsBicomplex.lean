import OAI.AlgebraicGeometry.Comparison.Betti.Sheaf.CechSectionsFunctor
import OAI.AlgebraicGeometry.Comparison.Betti.Sheaf.CechAugmentation
import OAI.AlgebraicGeometry.Comparison.Betti.TotalComplexFunctor

/-! # Cech Sections Bicomplex -/

namespace OAI.AlgebraicGeometry.Comparison.Betti.Sheaf.CechSectionsBicomplex

noncomputable section

/-! The sections isomorphism respects both differentials of the actual Čech double complex. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.TopologicalSpace

variable {X : TopCat.{0}} {ι : Type} (U : ι → Opens X)

instance sheafForget_additive : (TopCat.Sheaf.forget AddCommGrpCat.{0} X).Additive where
  map_add := by
    intro F G f g
    rfl

instance sheafCechPresheafFunctor_additive :
    (TopCat.Sheaf.forget AddCommGrpCat.{0} X ⋙ cechComplexFunctor U).Additive :=
  Functor.additive_of_iso (CechSectionsFunctor.sheafCechSectionsFunctorIso U)

def sheafCechSectionsBicomplexIso
    (K : CochainComplex (TopCat.Sheaf AddCommGrpCat.{0} X) ℕ) :
    TotalComplexFunctor.mapBicomplex Cech.FactorSections.sheafTopSections (CechAugmentation.sheafCechBicomplex U K) ≅
      ((TopCat.Sheaf.forget AddCommGrpCat.{0} X ⋙ cechComplexFunctor U).mapHomologicalComplex
        (.up ℕ)).obj K :=
  (NatIso.mapHomologicalComplex (CechSectionsFunctor.sheafCechSectionsFunctorIso U) (.up ℕ)).app K

theorem sheafCechSectionsBicomplexIso_f_f
    (K : CochainComplex (TopCat.Sheaf AddCommGrpCat.{0} X) ℕ) (q p : ℕ) :
    ((sheafCechSectionsBicomplexIso U K).hom.f q).f p =
      (CechSectionsFunctor.sheafCechSectionsIso U (K.X q)).hom.f p := rfl

end

end OAI.AlgebraicGeometry.Comparison.Betti.Sheaf.CechSectionsBicomplex

import OAI.AlgebraicGeometry.Picard.PoincareBundle.NormalizedDefectUnitLaws
import OAI.AlgebraicGeometry.Picard.PoincareBundle.Finite.GroupCocycleSplitting

/-! # Translation Cocycle -/

namespace OAI.AlgebraicGeometry.Picard.PoincareBundle.Symmetric.TranslationCocycle

noncomputable section

/-! A symmetric actual translation defect has a regular splitting on the original finite subgroup. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj

universe u

open OAI.AlgebraicGeometry.Picard.PoincareBundle.Line.Fibers OAI.AlgebraicGeometry.Picard.PoincareBundle.NormalizedKernelTranslation OAI.AlgebraicGeometry.Picard.PoincareBundle.Subgroup.DefectParameters
open OAI.AlgebraicGeometry.Picard.PoincareBundle.NormalizedTranslationUnit

variable {k : Type u} [Field k] [IsAlgClosed k]
  {H A : Over (Spec (.of k))} [GrpObj H] [IsCommMonObj H] [GrpObj A]
  [IsProper A.hom] [IsIntegral A.left]
  (i : H ⟶ A) [IsMonHom i] (L : Line.Bundles.LineBundle A.left)
  (t : Line.Fibers.fiber L (snd H A) ≅ Line.Fibers.fiber L (NormalizedKernelTranslation.action i))
  (hs : ∀ (T : Over (Spec (.of k))) (a b : T ⟶ H),
    Subgroup.DefectParameters.value i L (NormalizedTranslationUnit.translation i L t) a b = Subgroup.DefectParameters.value i L (NormalizedTranslationUnit.translation i L t) b a)

/-- Naturality, normalization, and the cocycle law are proved from the actual translation;
only symmetry of its regular defect is required here. -/
def cocycle : NaturalSchemeCocycle.NaturalCocycle H where
  value := Subgroup.DefectParameters.value i L (NormalizedTranslationUnit.translation i L t)
  natural := Subgroup.DefectParameters.value_natural i L (NormalizedTranslationUnit.translation i L t)
  one_left := NormalizedDefectUnitLaws.one_left i L t
  one_right := NormalizedDefectUnitLaws.one_right i L t
  symmetric := hs _
  cocycle := Subgroup.DefectCocycle.cocycle i L (NormalizedTranslationUnit.translation i L t)

include hs in
/-- A finite subgroup admits a natural regular correction of its symmetric translation defect. -/
theorem exists_correction [IsFinite H.hom] :
    ∃ v : ∀ T : Over (Spec (.of k)), (T ⟶ H) → Γ(T.left, ⊤)ˣ,
      (∀ T : Over (Spec (.of k)), v T 1 = 1) ∧
      (∀ {T U : Over (Spec (.of k))} (g : U ⟶ T) (a : T ⟶ H),
        Units.map g.left.appTop.hom (v T a) = v U (g ≫ a)) ∧
      ∀ (T : Over (Spec (.of k))) (a b : T ⟶ H),
        Subgroup.DefectParameters.value i L (NormalizedTranslationUnit.translation i L t) a b * v T (a * b) = v T a * v T b :=
  Finite.GroupCocycleSplitting.exists_splitting k H (TranslationCocycle.cocycle i L t hs)

end

end OAI.AlgebraicGeometry.Picard.PoincareBundle.Symmetric.TranslationCocycle

import OAI.NumberTheory.PadicHodge.IntegralComparison.Supported.SupportedRestriction
import Mathlib.CategoryTheory.Abelian.Projective.Resolution

/-! # Nonpositive Projective Resolution -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.NonpositiveProjectiveResolution

noncomputable section

/-! A genuine nonpositive cochain resolution becomes an ordinary
projective resolution by the index change n ↦ -n. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.HomologicalComplex

set_option backward.isDefEq.respectTransparency false

universe u v

variable {C : Type u} [Category.{v} C] [Abelian C]

abbrev shape := ComplexShape.embeddingUpIntLE 0
abbrev single := HomologicalComplex.single C (.up ℤ) 0

variable (M : C)

instance single_supported : (NonpositiveProjectiveResolution.single.obj M).IsStrictlySupported shape where
  isZero i hi := HomologicalComplex.isZero_single_obj_X (.up ℤ) 0 M i (by
    intro h
    subst i
    exact hi 0 (by simp [shape]))

def singleRestrictionIso : (NonpositiveProjectiveResolution.single.obj M).restriction shape ≅ (ChainComplex.single₀ C).obj M :=
  Hom.isoOfComponents (fun n => by
    by_cases hn : n = 0
    · subst n
      exact ((NonpositiveProjectiveResolution.single.obj M).restrictionXIso shape (i := 0) (i' := 0) (by simp [shape])) ≪≫
        singleObjXSelf (.up ℤ) 0 M ≪≫ (singleObjXSelf (.down ℕ) 0 M).symm
    · exact (isZero_single_obj_X (.up ℤ) 0 M (shape.f n) (by
        change (0 - (n : ℤ)) ≠ 0
        omega)).iso (isZero_single_obj_X (.down ℕ) 0 M n hn)) (by
    intro i j hij
    change _ ≫ ((ChainComplex.single₀ C).obj M).d i j =
      (NonpositiveProjectiveResolution.single.obj M).d (shape.f i) (shape.f j) ≫ _
    simp only [single_obj_d, comp_zero, zero_comp])

variable (K : CochainComplex C ℤ) [K.IsStrictlySupported shape]
  (ε : K ⟶ NonpositiveProjectiveResolution.single.obj M)

def augmentation : K.restriction shape ⟶ (ChainComplex.single₀ C).obj M :=
  restrictionMap ε shape ≫ (singleRestrictionIso M).hom

theorem augmentation_quasiIso [QuasiIso ε] : QuasiIso (augmentation M K ε) := by
  have : QuasiIso (restrictionMap ε shape) := Supported.SupportedRestriction.quasiIso shape K ε
  exact quasiIso_comp _ _

def ofComplex [∀ n : ℕ, Projective (K.X (shape.f n))] [QuasiIso ε] : ProjectiveResolution M where
  complex := K.restriction shape
  projective n := inferInstanceAs (Projective (K.X (shape.f n)))
  π := augmentation M K ε
  quasiIso := augmentation_quasiIso M K ε

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.NonpositiveProjectiveResolution

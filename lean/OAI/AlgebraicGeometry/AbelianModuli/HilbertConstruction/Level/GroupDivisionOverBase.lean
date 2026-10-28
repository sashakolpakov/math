import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.TorsionAnnihilatorDescent
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.MonoidHomEpiDescent
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.FaithfullyFlatTensorEpi

/-! # Group Division Over Base -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction

noncomputable section

/-! Division through full-level multiplication preserves the group law over arbitrary bases. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.CategoryTheory.MonoidalCategory
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj

universe u

variable {S : Scheme.{u}} {g h n : ℕ} (A : Abelian.Schemes.AbelianScheme g S) (B : Abelian.Schemes.AbelianScheme h S)

theorem Abelian.Schemes.AbelianScheme.fullLevel_division_isMonHom_overBase (level : A.FullLevel n)
    (m d : A.scheme ⟶ B.scheme) [IsMonHom m] (hd : A.multiplication n ≫ d = m) : IsMonHom d := by
  have : IsMonHom (A.multiplication n) := (A.fullLevelMultiplicationIsogeny level).preservesGroup
  have : Flat (A.multiplication n).left := (A.fullLevelMultiplicationIsogeny level).flat
  have : Surjective (A.multiplication n).left := (A.fullLevelMultiplicationIsogeny level).surjective
  have : Epi (A.multiplication n ⊗ₘ A.multiplication n) :=
    FaithfullyFlatTensorEpi.over_tensor_epi_of_flat_surjective (A.multiplication n) (A.multiplication n)
  exact MonoidHomEpiDescent.isMonHom_of_tensor_epi (A.multiplication n) m d hd

theorem Abelian.Schemes.AbelianScheme.fullLevel_existsUnique_groupDivision_overBase (level : A.FullLevel n)
    (m : A.scheme ⟶ B.scheme) [IsMonHom m] (hm : A.torsionInclusion n ≫ m = 1) :
    ∃! d : {f : A.scheme ⟶ B.scheme // IsMonHom f}, A.multiplication n ≫ d.val = m := by
  obtain ⟨d, hd, huniq⟩ := A.fullLevel_existsUnique_division B level m hm
  refine ⟨⟨d, A.fullLevel_division_isMonHom_overBase B level m d hd⟩, hd, ?_⟩
  intro e he
  exact Subtype.ext (huniq e.val he)

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction

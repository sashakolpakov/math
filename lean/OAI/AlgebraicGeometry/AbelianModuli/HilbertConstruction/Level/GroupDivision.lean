import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.TorsionAnnihilatorDescent
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Smooth.PointedMorphisms

/-! # Group Division -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction

noncomputable section

/-! Over a field, division through full-level multiplication is a group-scheme homomorphism. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.CategoryTheory.MonoidalCategory
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj

universe u

variable {K : Type u} [Field K] {g h n : ℕ}
variable (A : Abelian.Schemes.AbelianScheme g (Spec (.of K))) (B : Abelian.Schemes.AbelianScheme h (Spec (.of K)))

theorem Abelian.Schemes.AbelianScheme.fullLevel_division_isMonHom (level : A.FullLevel n) (m d : A.scheme ⟶ B.scheme)
    [IsMonHom m] (hd : A.multiplication n ≫ d = m) : IsMonHom d := by
  have : IsMonHom (A.multiplication n) := (A.fullLevelMultiplicationIsogeny level).preservesGroup
  apply Smooth.PointedMorphisms.abelianPointedMorphism_isMonHom A B d
  calc
    η[A.scheme] ≫ d = (η[A.scheme] ≫ A.multiplication n) ≫ d :=
      congrArg (fun f => f ≫ d) (IsMonHom.one_hom (A.multiplication n)).symm
    _ = η[A.scheme] ≫ m :=
      (Category.assoc _ _ _).trans (congrArg (fun f => η[A.scheme] ≫ f) hd)
    _ = η[B.scheme] := IsMonHom.one_hom m

theorem Abelian.Schemes.AbelianScheme.fullLevel_existsUnique_groupDivision (level : A.FullLevel n) (m : A.scheme ⟶ B.scheme)
    [IsMonHom m] (hm : A.torsionInclusion n ≫ m = 1) :
    ∃! d : {f : A.scheme ⟶ B.scheme // IsMonHom f}, A.multiplication n ≫ d.val = m := by
  obtain ⟨d, hd, huniq⟩ := A.fullLevel_existsUnique_division B level m hm
  refine ⟨⟨d, A.fullLevel_division_isMonHom B level m d hd⟩, hd, ?_⟩
  intro e he
  exact Subtype.ext (huniq e.val he)

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction

import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Polarized.TorsionHomRigidity
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Smooth.PointedMorphisms

/-! # Hom Division Uniqueness -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Polarized.HomDivisionUniqueness

noncomputable section

/-! Multiplication by a positive integer is injective on group homomorphisms into a polarized abelian variety. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj

universe u

variable {K : Type u} [Field K] {g h N : ℕ} {δ : Fin g → ℕ}
variable (A : PolarizationData.PolarizedAbelianWithFullLevel g δ N (Spec (.of K)))
variable (B : Abelian.Schemes.AbelianScheme h (Spec (.of K)))

theorem polarized_hom_pow_injective (f k : B.scheme ⟶ A.abelian.scheme) [IsMonHom f] [IsMonHom k]
    (n : ℕ) (hn : 0 < n) (hfk : f ^ n = k ^ n) : f = k := by
  have : IsMonHom (f / k) := by
    apply Smooth.PointedMorphisms.abelianPointedMorphism_isMonHom B A.abelian
    have he : η[B.scheme] ≫ (f / k) = η[A.abelian.scheme] / η[A.abelian.scheme] :=
      (GrpObj.comp_div η[B.scheme] f k).trans
        (congrArg₂ (fun a b : 𝟙_ (Over (Spec (.of K))) ⟶ A.abelian.scheme => a / b)
          (IsMonHom.one_hom f) (IsMonHom.one_hom k))
    have hη : (1 : 𝟙_ (Over (Spec (.of K))) ⟶ A.abelian.scheme) = η[A.abelian.scheme] := by
      simp [MonObj.one_eq_one]
    exact he.trans ((div_self' η[A.abelian.scheme]).trans hη)
  have hdiv : (f / k) ^ n = 1 := (div_pow f k n).trans
    ((congrArg (fun z : B.scheme ⟶ A.abelian.scheme => z / k ^ n) hfk).trans (div_self' (k ^ n)))
  exact div_eq_one.mp (TorsionHomRigidity.polarized_torsion_hom_eq_one A B (f / k) n hn hdiv)

theorem polarized_hom_multiplication_injective (f k : B.scheme ⟶ A.abelian.scheme)
    [IsMonHom f] [IsMonHom k] (n : ℕ) (hn : 0 < n)
    (hfk : f ≫ A.abelian.multiplication n = k ≫ A.abelian.multiplication n) : f = k :=
  polarized_hom_pow_injective A B f k n hn
    ((A.abelian.comp_multiplication n f).symm.trans (hfk.trans (A.abelian.comp_multiplication n k)))

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Polarized.HomDivisionUniqueness

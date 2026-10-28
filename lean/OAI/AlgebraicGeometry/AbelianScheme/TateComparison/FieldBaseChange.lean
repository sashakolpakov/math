import OAI.AlgebraicGeometry.AbelianScheme.TateComparison.TateBaseChange

/-! # Field Base Change -/

namespace OAI.AlgebraicGeometry.AbelianScheme.TateComparison.FieldBaseChange

noncomputable section

/-! Natural Tate isomorphisms between an abelian variety over an
algebraically closed characteristic-zero field and its actual base change. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj TensorProduct

variable {K k : Type} [Field K] [CharZero K] [IsAlgClosed K] [Field k]
  (b : Spec (.of k) ⟶ Spec (.of K)) (q : ℕ) [Fact q.Prime] {g g' : ℕ}
  (A : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g (Spec (.of K)))

def fieldBaseChangeTateEquiv :
    Add.schemeTateModule A.scheme (Over.mk (𝟙 (Spec (.of K)))) q ≃ₗ[ℤ_[q]]
      Add.schemeTateModule (A.pullback b).scheme (Over.mk (𝟙 (Spec (.of k)))) q :=
  (FieldExtension.abelianFieldTateEquiv (𝟙 (Spec (.of k)) ≫ b) q A).trans
    (TateBaseChange.baseChangeTateEquiv A b (Over.mk (𝟙 (Spec (.of k)))) q).symm

theorem fieldBaseChangeTateEquiv_toBase
    (z : Add.schemeTateModule A.scheme (Over.mk (𝟙 (Spec (.of K)))) q) :
    TateBaseChange.baseChangeTateEquiv A b (Over.mk (𝟙 (Spec (.of k)))) q
      (fieldBaseChangeTateEquiv b q A z) = FieldExtension.fieldTateMap (𝟙 (Spec (.of k)) ≫ b) A.scheme q z :=
  (TateBaseChange.baseChangeTateEquiv A b (Over.mk (𝟙 (Spec (.of k)))) q).apply_symm_apply _

theorem fieldBaseChangeTateEquiv_natural {B : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g' (Spec (.of K))}
    (a : A.scheme ⟶ B.scheme) [IsMonHom a]
    (z : Add.schemeTateModule A.scheme (Over.mk (𝟙 (Spec (.of K)))) q) :
    fieldBaseChangeTateEquiv b q B
        (Add.schemeTateMap A.scheme (Over.mk (𝟙 (Spec (.of K)))) q a z) =
      Add.schemeTateMap (A.pullback b).scheme (B := (B.pullback b).scheme)
        (Over.mk (𝟙 (Spec (.of k)))) q ((Over.pullback b).map a)
          (fieldBaseChangeTateEquiv b q A z) := by
  apply (TateBaseChange.baseChangeTateEquiv B b (Over.mk (𝟙 (Spec (.of k)))) q).injective
  rw [fieldBaseChangeTateEquiv_toBase, TateBaseChange.baseChangeTateEquiv_natural,
    fieldBaseChangeTateEquiv_toBase]
  exact LinearMap.congr_fun (FieldExtension.fieldTateMap_natural (𝟙 (Spec (.of k)) ≫ b) A.scheme q a) z

def fieldBaseChangeRationalTateEquiv :
    Rational.rationalTateModule A.scheme (Over.mk (𝟙 (Spec (.of K)))) q ≃ₗ[ℚ_[q]]
      Rational.rationalTateModule (A.pullback b).scheme (Over.mk (𝟙 (Spec (.of k)))) q :=
  LinearEquiv.baseChange ℤ_[q] ℚ_[q] _ _ (fieldBaseChangeTateEquiv b q A)

theorem fieldBaseChangeRationalTateEquiv_natural {B : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g' (Spec (.of K))}
    (a : A.scheme ⟶ B.scheme) [IsMonHom a]
    (z : Rational.rationalTateModule A.scheme (Over.mk (𝟙 (Spec (.of K)))) q) :
    fieldBaseChangeRationalTateEquiv b q B
        (Rational.rationalTateMap (T := Over.mk (𝟙 (Spec (.of K)))) (q := q) a z) =
      Rational.rationalTateMap (A := (A.pullback b).scheme) (B := (B.pullback b).scheme)
        (T := Over.mk (𝟙 (Spec (.of k)))) (q := q) ((Over.pullback b).map a)
          (fieldBaseChangeRationalTateEquiv b q A z) := by
  induction z using TensorProduct.inductionOn with
  | add z w hz hw => simp only [LinearEquiv.map_add, LinearMap.map_add, hz, hw]
  | tmul c z =>
    change c ⊗ₜ[ℤ_[q]] fieldBaseChangeTateEquiv b q B
        (Add.schemeTateMap A.scheme (Over.mk (𝟙 (Spec (.of K)))) q a z) =
      c ⊗ₜ[ℤ_[q]] Add.schemeTateMap (A.pullback b).scheme (B := (B.pullback b).scheme)
        (Over.mk (𝟙 (Spec (.of k)))) q ((Over.pullback b).map a)
          (fieldBaseChangeTateEquiv b q A z)
    rw [fieldBaseChangeTateEquiv_natural]

end

end OAI.AlgebraicGeometry.AbelianScheme.TateComparison.FieldBaseChange

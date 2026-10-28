import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.SymmetricGraphInducingFormula
import OAI.AlgebraicGeometry.Picard.PoincareBundle.InducingPullback
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Finite.TorsionHomCancellation
import OAI.AlgebraicGeometry.FormalGeometry.Completion.Multiplication

/-! # Symmetric Graph Descent Cancellation -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.SymmetricGraphDescentCancellation

noncomputable section

/-! The actual descent of the squared graph line along multiplication by
two induces the original homomorphism, by cancellation of finite torsion. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj
universe u
open OAI.AlgebraicGeometry.Picard.PoincareBundle.InducingClass.Bundle

local instance graphDescentPicardCommGroup (X : Scheme.{u}) : CommGroup (Line.Bundles.LineBundle.IsoClass X) :=
  Picard.Homomorphisms.SchemeGroup.Construction.lineBundleClassCommGroup X

theorem inducingLineClass_tensor_self {S : Scheme.{u}} (B : Over S) [GrpObj B]
    (L : Line.Bundles.LineBundle B.left) : Picard.PoincareBundle.InducingClass.Bundle.lineClass B (L.tensor L) = Picard.PoincareBundle.InducingClass.Bundle.lineClass B L ^ 2 := by
  unfold Picard.PoincareBundle.InducingClass.Bundle.lineClass
  rw [Line.Bundles.LineBundle.classOf_tensor]
  simp only [map_mul, div_eq_mul_inv, mul_inv_rev, pow_two]
  ac_rfl

theorem inducingLineClass_congr {S : Scheme.{u}} (B : Over S) [GrpObj B]
    {L M : Line.Bundles.LineBundle B.left} (h : Line.Bundles.LineBundle.classOf L = Line.Bundles.LineBundle.classOf M) :
    Picard.PoincareBundle.InducingClass.Bundle.lineClass B L = Picard.PoincareBundle.InducingClass.Bundle.lineClass B M := by
  simp only [Picard.PoincareBundle.InducingClass.Bundle.lineClass, h]

variable {K : Type u} [Field K] {g : ℕ}
  {A : Abelian.Schemes.AbelianScheme g (Spec (.of K))}

theorem poincareAt_multiplicationProduct_class (D : Dual.Data.DualAbelianData A)
    (q : A.scheme ⟶ D.abelian.scheme) [IsMonHom q] (n : ℕ) :
    Picard.Homomorphisms.SchemePullback.Construction.schemePicardPullback (A.multiplication n ⊗ₘ A.multiplication n).left
      (Line.Bundles.LineBundle.classOf (D.poincareAt q)) =
        Line.Bundles.LineBundle.classOf (D.poincareAt (q ^ (n * n))) := by
  let X := A.scheme ⊗ A.scheme
  let x := fst A.scheme A.scheme
  let y := snd A.scheme A.scheme
  let m := A.multiplication n
  let z := m ⊗ₘ m
  have hx : z ≫ x = x ^ n :=
    (tensorHom_fst m m).trans (A.comp_multiplication n x)
  have hy : z ≫ y = y ^ n :=
    (tensorHom_snd m m).trans (A.comp_multiplication n y)
  have h₁ := congrArg (Line.Bundles.LineBundle.pullbackClass z.left)
    (Polarization.ClassPairing.poincareAt_class_eq_pair_projections D q)
  have h₂ := Polarization.ClassPairing.polarizationPairClass_naturality D q x y z
  have h₃ : Polarization.ClassPairing.polarizationPairClass D q X (z ≫ x) (z ≫ y) =
      Polarization.ClassPairing.polarizationPairClass D q X (x ^ n) (y ^ n) := by rw [hx, hy]
  have h₄ : Polarization.ClassPairing.polarizationPairClass D q X (x ^ n) (y ^ n) =
      Polarization.ClassPairing.polarizationPairClass D q X x y ^ (n * n) := by
    change D.poincarePairClass X ((x ^ n) ≫ q) (y ^ n) =
      D.poincarePairClass X (x ≫ q) y ^ (n * n)
    rw [MonObj.pow_comp]
    exact D.poincarePairClass_pow X (x ≫ q) y n n
  have h₅ := congrArg (fun c : Line.Bundles.LineBundle.IsoClass X.left => c ^ (n * n))
    (Polarization.ClassPairing.poincareAt_class_eq_pair_projections D q).symm
  have h₆ := (D.poincareAt_class_pow A.scheme q (n * n)).symm
  exact h₁.trans (h₂.trans (h₃.trans (h₄.trans (h₅.trans h₆))))

theorem hom_eq_of_graphTensorSquare_descent
    (D : Dual.Data.DualAbelianData A)
    (p q : A.scheme ⟶ D.abelian.scheme) [IsMonHom p] [IsMonHom q]
    (hs : ∀ x y : A.scheme ⊗ A.scheme ⟶ A.scheme,
      D.poincarePairClass (A.scheme ⊗ A.scheme) (x ≫ p) y =
        D.poincarePairClass (A.scheme ⊗ A.scheme) (y ≫ p) x)
    (h4 : (4 : K) ≠ 0) (M : Line.Bundles.LineBundle A.scheme.left)
    (eM : (((D.poincareAt q).tensor (M.pullback (fst A.scheme A.scheme).left)).tensor
      (M.pullback (snd A.scheme A.scheme).left)).sheaf ≅ (M.pullback μ[A.scheme].left).sheaf)
    (e : (M.pullback (A.multiplication 2).left).sheaf ≅
      ((PoincareGraph.Bundles.poincareGraphBundle D p).tensor (PoincareGraph.Bundles.poincareGraphBundle D p)).sheaf) : q = p := by
  let Q := PoincareGraph.Bundles.poincareGraphBundle D p
  let m := A.multiplication 2
  let : IsMonHom m := FormalGeometry.Completion.Multiplication.Construction.multiplication_isMonHom A.scheme 2
  let z := m ⊗ₘ m
  have he : Line.Bundles.LineBundle.classOf (M.pullback m.left) = Line.Bundles.LineBundle.classOf (Q.tensor Q) :=
    Quotient.sound ⟨e⟩
  have hM : Line.Bundles.LineBundle.classOf (D.poincareAt q) = Picard.PoincareBundle.InducingClass.Bundle.lineClass A.scheme M :=
    Picard.PoincareBundle.InducingClass.Bundle.class_eq_of_formula A.scheme M (D.poincareAt q) eM
  have hQ : Picard.PoincareBundle.InducingClass.Bundle.lineClass A.scheme Q = Line.Bundles.LineBundle.classOf (D.poincareAt (p ^ 2)) :=
    SymmetricGraphInducingFormula.poincareGraph_differenceClass_double D p hs
  have hpowers : q ^ 4 = p ^ 4 := by
    apply D.poincareAt_class_injective A.scheme
    have h₁ := (poincareAt_multiplicationProduct_class D q 2).symm
    have h₂ := congrArg (Picard.Homomorphisms.SchemePullback.Construction.schemePicardPullback z.left) hM
    have h₃ := Picard.PoincareBundle.InducingPullback.Bundle.lineClass_pullback m M
    have h₄ := inducingLineClass_congr A.scheme he
    have h₅ := inducingLineClass_tensor_self A.scheme Q
    have h₆ := congrArg (fun c : Line.Bundles.LineBundle.IsoClass (A.scheme ⊗ A.scheme).left => c ^ 2) hQ
    have h₇ : Line.Bundles.LineBundle.classOf (D.poincareAt (p ^ 2)) ^ 2 =
        Line.Bundles.LineBundle.classOf (D.poincareAt (p ^ 4)) := by
      have hp : (p ^ 2) ^ 2 = p ^ 4 := (pow_mul p 2 2).symm
      exact (D.poincareAt_class_pow A.scheme (p ^ 2) 2).symm.trans
        (congrArg (fun f : A.scheme ⟶ D.abelian.scheme => Line.Bundles.LineBundle.classOf (D.poincareAt f)) hp)
    exact h₁.trans (h₂.trans (h₃.trans (h₄.trans (h₅.trans (h₆.trans h₇)))))
  let : IsFinite (D.abelian.multiplication 4).left :=
    FormalGeometry.Completion.Multiplication.Construction.multiplication_isFinite D.abelian.scheme 4 h4
  let : IsFinite (D.abelian.torsionScheme 4).hom :=
    inferInstanceAs (IsFinite (Limits.pullback.snd
      (D.abelian.multiplication 4).left η[D.abelian.scheme].left))
  exact Finite.TorsionHomCancellation.abelian_hom_pow_injective_of_finite_torsion A D.abelian 4 q p hpowers

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.SymmetricGraphDescentCancellation

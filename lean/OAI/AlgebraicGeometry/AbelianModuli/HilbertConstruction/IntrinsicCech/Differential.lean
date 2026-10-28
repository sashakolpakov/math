/-
Derived from AINTLIB:
  projects/ModularCurves/ModularCurves/ForMathlib/SheafCechDifferential.lean
The upstream AINTLIB repository is licensed under Apache 2.0.
This file has been modified.
-/
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.IntrinsicCech.Cofaces

/-! # Differential -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.IntrinsicCech.Differential

noncomputable section

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.TopologicalSpace Opposite
universe u
variable {T : Type u} [TopologicalSpace T]
variable (F : (Opens T)ᵒᵖ ⥤ AddCommGrpCat.{u}) {ι : Type u}
variable (U : ι → Opens T) (n : ℕ)

/-- Under the concrete cochain equivalence, the Cech differential is the alternating
sum of restrictions along all tuple deletions. -/
theorem nativeCechDifferential_apply (x : ((cechComplexFunctor U).obj F).X n)
    (i : Fin (n + 2) → ι) :
    Cochains.cechCochainAddEquiv F U (n + 1)
        (((cechComplexFunctor U).obj F).d n (n + 1) x) i =
      ∑ k : Fin (n + 2), (-1 : ℤ) ^ (k : ℕ) •
        F.map (((FormalCoproduct.mk _ U).mapPower
          (SimplexCategory.δ k).toOrderHom.toFun).φ i).op
          (Cochains.cechCochainAddEquiv F U n x
            (i ∘ (SimplexCategory.δ k).toOrderHom.toFun)) := by
  rw [Cofaces.cechDifferential_eq]
  have hmapSum :
      Cochains.cechCochainAddEquiv F U (n + 1)
          (∑ k : Fin (n + 2),
            (((-1 : ℤ) ^ (k : ℕ) •
              ((FormalCoproduct.cosimplicialObjectFunctor
                (FormalCoproduct.mk _ U).cech).obj F).δ k) x)) =
        ∑ k : Fin (n + 2), Cochains.cechCochainAddEquiv F U (n + 1)
          (((-1 : ℤ) ^ (k : ℕ) •
            ((FormalCoproduct.cosimplicialObjectFunctor
              (FormalCoproduct.mk _ U).cech).obj F).δ k) x) := by
    exact map_sum (Cochains.cechCochainAddEquiv F U (n + 1)) _ Finset.univ
  calc
    _ = Cochains.cechCochainAddEquiv F U (n + 1)
        (∑ k : Fin (n + 2),
          ((-1 : ℤ) ^ (k : ℕ) •
            ((FormalCoproduct.cosimplicialObjectFunctor
              (FormalCoproduct.mk _ U).cech).obj F).δ k) x) i :=
      congrArg (fun y => Cochains.cechCochainAddEquiv F U (n + 1) y i)
        (Cofaces.addCommGrp_sum_apply _ x)
    _ = (∑ k : Fin (n + 2),
        Cochains.cechCochainAddEquiv F U (n + 1)
          (((-1 : ℤ) ^ (k : ℕ) •
            ((FormalCoproduct.cosimplicialObjectFunctor
              (FormalCoproduct.mk _ U).cech).obj F).δ k) x)) i := by
      exact congrFun hmapSum i
    _ = ∑ k : Fin (n + 2),
        Cochains.cechCochainAddEquiv F U (n + 1)
          (((-1 : ℤ) ^ (k : ℕ) •
            ((FormalCoproduct.cosimplicialObjectFunctor
              (FormalCoproduct.mk _ U).cech).obj F).δ k) x) i :=
      Finset.sum_apply i Finset.univ _
    _ = _ := by
      apply Finset.sum_congr rfl
      intro k hk
      calc
        Cochains.cechCochainAddEquiv F U (n + 1)
            (((-1 : ℤ) ^ (k : ℕ) •
              ((FormalCoproduct.cosimplicialObjectFunctor
                (FormalCoproduct.mk _ U).cech).obj F).δ k) x) i =
          Cochains.cechCochainAddEquiv F U (n + 1)
            ((-1 : ℤ) ^ (k : ℕ) •
              (((FormalCoproduct.cosimplicialObjectFunctor
                (FormalCoproduct.mk _ U).cech).obj F).δ k x)) i :=
            congrArg (fun y => Cochains.cechCochainAddEquiv F U (n + 1) y i)
              (show
                ((-1 : ℤ) ^ (k : ℕ) •
                  ((FormalCoproduct.cosimplicialObjectFunctor
                    (FormalCoproduct.mk _ U).cech).obj F).δ k) x =
                  (-1 : ℤ) ^ (k : ℕ) •
                    (((FormalCoproduct.cosimplicialObjectFunctor
                      (FormalCoproduct.mk _ U).cech).obj F).δ k x) from rfl)
        _ = (-1 : ℤ) ^ (k : ℕ) •
            Cochains.cechCochainAddEquiv F U (n + 1)
              (((FormalCoproduct.cosimplicialObjectFunctor
                (FormalCoproduct.mk _ U).cech).obj F).δ k x) i :=
          congrFun (map_zsmul (Cochains.cechCochainAddEquiv F U (n + 1))
            ((-1 : ℤ) ^ (k : ℕ))
            (((FormalCoproduct.cosimplicialObjectFunctor
              (FormalCoproduct.mk _ U).cech).obj F).δ k x)) i
        _ = _ := congrArg (fun y => (-1 : ℤ) ^ (k : ℕ) • y)
          (Cofaces.nativeCechCoface_apply F U n x k i)

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.IntrinsicCech.Differential

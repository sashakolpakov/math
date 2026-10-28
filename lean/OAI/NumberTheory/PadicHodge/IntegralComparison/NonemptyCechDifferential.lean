import OAI.NumberTheory.PadicHodge.IntegralComparison.NonemptyCechNerve

/-! # Nonempty Cech Differential -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.NonemptyCechDifferential

noncomputable section

/-! The literal differential of the original nonempty Čech complex,
in its universal product projections. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits Opposite
open scoped Simplicial

universe u v w z t
variable {C : Type u} [Category.{v} C] [HasBinaryProducts C]
  {A : Type w} [Category.{z} A] [Preadditive A] [HasProducts.{t} A]
  {ι : Type t} (U : ι → C) (P : Cᵒᵖ ⥤ A)

abbrev object (n : ℕ) := (NonemptyCechNerve.nerve U).obj (op ⦋n⦌)
abbrev coefficients (n : ℕ) (a : (object U n).I) := P.obj (op ((object U n).obj a))
abbrev complex := (NonemptyCechNerve.complexFunctor U).obj P

def projection (n : ℕ) (a : Fin (n + 1) → ι) :
    (complex U P).X n ⟶ P.obj (op (∏ᶜ (U ∘ a))) :=
  Pi.π (fun b : Fin (n + 1) → ι => P.obj (op (∏ᶜ (U ∘ b)))) a

def face (n : ℕ) (i : Fin (n + 2)) :=
  (NonemptyCechNerve.nerve U).map (SimplexCategory.δ i).op

def faceMap (n : ℕ) (i : Fin (n + 2)) (a : Fin (n + 2) → ι) :
    (∏ᶜ (U ∘ a)) ⟶ ∏ᶜ (U ∘ (a ∘ i.succAbove)) :=
  Pi.lift (fun j : Fin (n + 1) => Pi.π (U ∘ a) (i.succAbove j))

theorem coface_projection (n : ℕ) (i : Fin (n + 2)) (a : Fin (n + 2) → ι) :
    (((FormalCoproduct.cosimplicialObjectFunctor (NonemptyCechNerve.nerve U)).obj P).map
        (SimplexCategory.δ i)) ≫ projection U P (n + 1) a =
      projection U P n (a ∘ i.succAbove) ≫ P.map (faceMap U n i a).op := by
  exact Pi.lift_comp_π _ a

theorem differential (n : ℕ) :
    (complex U P).d n (n + 1) =
      ∑ i : Fin (n + 2), (-1 : ℤ)^i.val •
        (((FormalCoproduct.cosimplicialObjectFunctor (NonemptyCechNerve.nerve U)).obj P).map
          (SimplexCategory.δ i)) := by
  change (AlgebraicTopology.AlternatingCofaceMapComplex.obj _).d n (n + 1) = _
  dsimp only [AlgebraicTopology.AlternatingCofaceMapComplex.obj]
  rw [CochainComplex.of_d]
  rfl

omit [HasProducts A] in
private theorem sum_comp {X Y Z : A} {n : ℕ} (f : Fin n → (X ⟶ Y))
    (a : Fin n → ℤ) (g : Y ⟶ Z) :
    (∑ i, a i • f i) ≫ g = ∑ i, a i • (f i ≫ g) := by
  simp only [Preadditive.sum_comp, Preadditive.zsmul_comp]

theorem differential_projection (n : ℕ) (a : Fin (n + 2) → ι) :
    (complex U P).d n (n + 1) ≫ projection U P (n + 1) a =
      ∑ i : Fin (n + 2), (-1 : ℤ)^i.val •
        (projection U P n (a ∘ i.succAbove) ≫ P.map (faceMap U n i a).op) := by
  exact (congrArg (fun f => f ≫ projection U P (n + 1) a) (differential U P n)).trans
    ((NonemptyCechDifferential.sum_comp _ _ _).trans (Finset.sum_congr rfl (fun i _ =>
      congrArg (fun f => (-1 : ℤ)^i.val • f) (coface_projection U P n i a))))

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.NonemptyCechDifferential

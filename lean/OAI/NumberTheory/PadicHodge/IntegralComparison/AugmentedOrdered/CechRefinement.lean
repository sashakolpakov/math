import OAI.NumberTheory.PadicHodge.IntegralComparison.OrderedCech.Refinement
import OAI.NumberTheory.PadicHodge.IntegralComparison.AugmentedOrdered.CechZero
import OAI.NumberTheory.PadicHodge.IntegralComparison.Cochain.TailQuasiIso

/-! # Cech Refinement -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.AugmentedOrdered.CechRefinement

noncomputable section

/-! Refinement of the supported ordered Čech complex fixes its ambient
section term and uses the original ordered refinement in positive degrees. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.CategoryTheory.Preadditive Opposite
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

private theorem three_projection {A : Type*} [Category A]
    {P Q R S T W : A} {a : P ⟶ Q} {b : Q ⟶ R} {c : R ⟶ S}
    {p : S ⟶ T} {q : R ⟶ T} {s : Q ⟶ W} {t : P ⟶ W} {z : W ⟶ T}
    (hc : c ≫ p = q) (hb : b ≫ q = s ≫ z) (ha : a ≫ s = t) :
    (a ≫ b ≫ c) ≫ p = t ≫ z := by
  simp only [Category.assoc]
  rw [hc, hb, ← Category.assoc, ha]

universe u v
variable {C : Type u} [Preorder C] [HasFiniteProducts C]
  {D : Type v} [Category D] [Abelian D] [HasProducts.{u} D] [HasCoproducts.{0} D]
  {ι κ : Type u} [LinearOrder ι] [LinearOrder κ]
  (U : ι → C) (V : κ → C)
  (r : FormalCoproduct.mk κ V ⟶ FormalCoproduct.mk ι U) (P : Cᵒᵖ ⥤ D)

open OAI.NumberTheory.PadicHodge.IntegralComparison.AugmentedOrdered.CechZero

omit [HasCoproducts D] in
private theorem inclusion_projection {n : ℕ} (a : Fin (n + 1) → ι) (ha : StrictMono a) :
    OrderedCech.Retraction.inclusionF U P n ≫ Cech.TupleRestrictionFunctor.projection U P a =
      OrderedCech.Projection.projection U P n ⟨a, ha⟩ := by
  unfold OrderedCech.Retraction.inclusionF
  erw [Category.assoc, Cech.SortedProjection.projection_strictMono U P n a ha,
    OrderedCech.Projection.zeroExtension_projection U P n a ha]

private def intersectionMap (a : Fin 1 → κ) :
    (∏ᶜ (V ∘ a)) ⟶ ∏ᶜ (U ∘ (r.f ∘ a)) :=
  ((GeometricComparison.NonemptyCech.Refinement.NonemptyCechRefinement.nerveMap U V r).app (op (SimplexCategory.mk 0))).φ a

omit [HasCoproducts D] in
private theorem positive_zero_projection (a : OrderedCech.Projection.Index (ι := κ) 0) :
    (OrderedCech.Refinement.map U V r P).f 0 ≫
      OrderedCech.Projection.projection V P 0 a =
    OrderedCech.Projection.projection U P 0
        ⟨r.f ∘ a.val, (by intro i j hij; have _hi := i.isLt; have _hj := j.isLt; omega)⟩ ≫ P.map (intersectionMap U V r a.val).op := by
  have h : (GeometricComparison.NonemptyCech.Refinement.NonemptyCechRefinement.map U V r P).f 0 ≫
      Cech.TupleRestrictionFunctor.projection V P a.val =
    Cech.TupleRestrictionFunctor.projection U P (r.f ∘ a.val) ≫
      P.map (intersectionMap U V r a.val).op := Pi.lift_comp_π _ a.val
  exact three_projection (OrderedCech.Projection.mapF_projection V P 0 a) h
    (inclusion_projection U P (r.f ∘ a.val) (by
      intro i j hij
      have hi := i.isLt
      have hj := j.isLt
      omega))

omit [HasCoproducts D] in
private theorem zero_restriction (a : OrderedCech.Projection.Index (ι := ι) 0) :
    (CechZero.zeroIso U P).inv ≫ Cech.differential U P 0 ≫ OrderedCech.Projection.projection U P 0 a =
      P.map (terminal.from (∏ᶜ (U ∘ a.val))).op :=
  CechZero.zeroIso_inv_differential_π U P a

def mapF : (n : ℕ) → Cech.object U P n ⟶ Cech.object V P n
  | 0 => (CechZero.zeroIso U P).hom ≫ (CechZero.zeroIso V P).inv
  | n + 1 => (OrderedCech.Refinement.map U V r P).f n

omit [HasCoproducts D] in
private theorem mapF_zero_d : mapF U V r P 0 ≫ Cech.differential V P 0 =
    Cech.differential U P 0 ≫ mapF U V r P 1 := by
  apply (cancel_epi (CechZero.zeroIso U P).inv).mp
  change (CechZero.zeroIso U P).inv ≫ ((CechZero.zeroIso U P).hom ≫ (CechZero.zeroIso V P).inv) ≫ Cech.differential V P 0 =
    (CechZero.zeroIso U P).inv ≫ Cech.differential U P 0 ≫ (OrderedCech.Refinement.map U V r P).f 0
  erw [Category.assoc, Iso.inv_hom_id_assoc]
  apply Pi.hom_ext
  intro (a : OrderedCech.Projection.Index (ι := κ) 0)
  change ((CechZero.zeroIso V P).inv ≫ Cech.differential V P 0) ≫ OrderedCech.Projection.projection V P 0 a =
    ((CechZero.zeroIso U P).inv ≫ Cech.differential U P 0 ≫ (OrderedCech.Refinement.map U V r P).f 0) ≫
      OrderedCech.Projection.projection V P 0 a
  erw [Category.assoc, zero_restriction, Category.assoc, Category.assoc, positive_zero_projection,
    ← Category.assoc, ← Category.assoc]
  erw [Category.assoc (CechZero.zeroIso U P).inv, zero_restriction, ← P.map_comp, ← op_comp]
  congr 1

def map : Cech.complex U P ⟶ Cech.complex V P :=
  CochainComplex.ofHom (mapF U V r P) (fun n => by
    cases n with
    | zero =>
      change mapF U V r P 0 ≫ (Cech.complex V P).d 0 (0 + 1) =
        (Cech.complex U P).d 0 (0 + 1) ≫ mapF U V r P 1
      rw [show (Cech.complex V P).d 0 (0 + 1) = Cech.differential V P 0 from CochainComplex.of_d (Cech.object V P) (Cech.differential V P) 0,
        show (Cech.complex U P).d 0 (0 + 1) = Cech.differential U P 0 from CochainComplex.of_d (Cech.object U P) (Cech.differential U P) 0]
      exact mapF_zero_d U V r P
    | succ n => simpa only [Cech.complex, CochainComplex.of_d, mapF,
        OrderedCech.Projection.complex, OrderedCech.Projection.differential] using
        (OrderedCech.Refinement.map U V r P).comm n (n + 1))

omit [HasCoproducts D] in
@[simp] theorem map_f_zero : (CechRefinement.map U V r P).f 0 = (CechZero.zeroIso U P).hom ≫ (CechZero.zeroIso V P).inv := rfl
omit [HasCoproducts D] in
@[simp] theorem map_f_succ (n : ℕ) : (CechRefinement.map U V r P).f (n + 1) =
    (OrderedCech.Refinement.map U V r P).f n := rfl

omit [HasCoproducts D] in
theorem map_zero : (CechRefinement.map U V r P).f 0 ≫ (CechZero.zeroIso V P).hom = (CechZero.zeroIso U P).hom := by
  change ((CechZero.zeroIso U P).hom ≫ (CechZero.zeroIso V P).inv) ≫ (CechZero.zeroIso V P).hom = _
  erw [Category.assoc, Iso.inv_hom_id, Category.comp_id]

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.AugmentedOrdered.CechRefinement

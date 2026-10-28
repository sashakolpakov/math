import OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.BlockProducts

/-! # Product Points -/

namespace OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.ProductPoints.Construction

noncomputable section

/-!
The explicit finite block product represents tuples of points on every
test scheme. Both the multiplication and test-scheme naturality are kept.
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry Opposite
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj

universe u

variable {S : Scheme.{u}}

def groupPairPointsEquiv (G H : Grp (Over S)) (T : Over S) :
    (T ⟶ (G ⊗ H).X) ≃* ((T ⟶ G.X) × (T ⟶ H.X)) where
  toFun a := (a ≫ fst G.X H.X, a ≫ snd G.X H.X)
  invFun a := lift a.1 a.2
  left_inv a := (comp_lift a (fst G.X H.X) (snd G.X H.X)).symm.trans
    ((congrArg (fun f => a ≫ f) lift_fst_snd).trans (Category.comp_id a))
  right_inv a := by simp only [lift_fst, lift_snd]
  map_mul' a b := by
    change T ⟶ G.X ⊗ H.X at a b
    exact Prod.ext (MonObj.mul_comp a b (fst G.X H.X)) (MonObj.mul_comp a b (snd G.X H.X))

def tuplePairsMulEquiv {I : Type*} (P : I × Bool → Type*) [∀ v, Mul (P v)] :
    (∀ v, P (v, false) × P (v, true)) ≃* (∀ v, P v) where
  toFun f v := match v with | (i, false) => (f i).1 | (i, true) => (f i).2
  invFun f v := (f (v, false), f (v, true))
  left_inv _ := rfl
  right_inv f := by funext ⟨v, b⟩; cases b <;> rfl
  map_mul' _ _ := by funext ⟨v, b⟩; cases b <;> rfl

def piReindexMulEquiv {I J : Type*} (P : J → Type*) [∀ v, Mul (P v)] (e : I ≃ J) :
    (∀ v, P (e v)) ≃* (∀ v, P v) where
  toEquiv := Equiv.piCongrLeft P e
  map_mul' a b := by
    funext v
    obtain ⟨w, rfl⟩ := e.surjective v
    exact (Equiv.piCongrLeft_apply_apply P e (a * b) w).trans
      (congrArg₂ (· * ·) (Equiv.piCongrLeft_apply_apply P e a w).symm
        (Equiv.piCongrLeft_apply_apply P e b w).symm)

def groupBlockProductPointsEquiv : (n : ℕ) → (B : Fin n → Grp (Over S)) → (T : Over S) →
    (T ⟶ (BlockProducts.Construction.groupBlockProduct n B).X) ≃* (∀ v, T ⟶ (B v).X)
  | 0, _, T =>
    { toFun := fun _ v => Fin.elim0 v
      invFun := fun _ => toUnit T
      left_inv := fun _ => toUnit_unique _ _
      right_inv := fun _ => funext (fun v => Fin.elim0 v)
      map_mul' := fun _ _ => funext (fun v => Fin.elim0 v) }
  | n + 1, B, T =>
    let C := BlockProducts.Construction.groupBlockProduct n (fun v => B v.succ)
    let e := groupBlockProductPointsEquiv n (fun v => B v.succ) T
    { toFun := fun a => Fin.cons (a ≫ fst (B 0).X C.X) (e (a ≫ snd (B 0).X C.X))
      invFun := fun b => lift (b 0) (e.symm (fun v => b v.succ))
      left_inv := by
        intro a
        apply CartesianMonoidalCategory.hom_ext
        · exact lift_fst _ _
        · exact (lift_snd _ _).trans (e.symm_apply_apply _)
      right_inv := by
        intro b
        funext v
        refine Fin.cases ?_ (fun w => ?_) v
        · exact lift_fst _ _
        · exact congrFun ((congrArg e (lift_snd (b 0) (e.symm (fun w => b w.succ)))).trans
            (e.apply_symm_apply _)) w
      map_mul' := by
        intro a b
        change T ⟶ (B 0).X ⊗ C.X at a b
        funext v
        refine Fin.cases ?_ (fun w => ?_) v
        · exact MonObj.mul_comp a b (fst (B 0).X C.X)
        · exact congrFun ((congrArg e (MonObj.mul_comp a b (snd (B 0).X C.X))).trans
            (e.map_mul _ _)) w }

theorem groupBlockProductPointsEquiv_natural (n : ℕ) (B : Fin n → Grp (Over S))
    {T U : Over S} (f : T ⟶ U) (a : U ⟶ (BlockProducts.Construction.groupBlockProduct n B).X) (v : Fin n) :
    Construction.groupBlockProductPointsEquiv n B T (f ≫ a) v =
      f ≫ Construction.groupBlockProductPointsEquiv n B U a v := by
  induction n with
  | zero => exact Fin.elim0 v
  | succ n ih =>
    refine Fin.cases ?_ (fun w => ?_) v
    · exact Category.assoc f a (fst (B 0).X (BlockProducts.Construction.groupBlockProduct n (fun w => B w.succ)).X)
    · change Construction.groupBlockProductPointsEquiv n (fun w => B w.succ) T
        ((f ≫ a) ≫ snd (B 0).X (BlockProducts.Construction.groupBlockProduct n (fun w => B w.succ)).X) w = _
      exact (congrArg (fun z => Construction.groupBlockProductPointsEquiv n (fun w => B w.succ) T z w)
        (Category.assoc f a (snd (B 0).X (BlockProducts.Construction.groupBlockProduct n (fun w => B w.succ)).X))).trans
          (ih _ _ w)

/-- Product inclusions act on each test-scheme coordinate separately. -/
theorem groupBlockProductPointsEquiv_map (n : ℕ) (B C : Fin n → Grp (Over S))
    (f : ∀ v, B v ⟶ C v) (T : Over S) (a : T ⟶ (BlockProducts.Construction.groupBlockProduct n B).X) (v : Fin n) :
    Construction.groupBlockProductPointsEquiv n C T (a ≫ (BlockProducts.Construction.groupBlockProductMap n B C f).hom.hom) v =
      Construction.groupBlockProductPointsEquiv n B T a v ≫ (f v).hom.hom := by
  induction n with
  | zero => exact Fin.elim0 v
  | succ n ih =>
    let B' := BlockProducts.Construction.groupBlockProduct n (fun w => B w.succ)
    let C' := BlockProducts.Construction.groupBlockProduct n (fun w => C w.succ)
    let f' := (BlockProducts.Construction.groupBlockProductMap n (fun w => B w.succ) (fun w => C w.succ)
      (fun w => f w.succ)).hom.hom
    refine Fin.cases ?_ (fun w => ?_) v
    · change (a ≫ ((f 0).hom.hom ⊗ₘ f')) ≫ fst (C 0).X C'.X =
        (a ≫ fst (B 0).X B'.X) ≫ (f 0).hom.hom
      exact (Category.assoc a ((f 0).hom.hom ⊗ₘ f') (fst (C 0).X C'.X)).trans
        ((congrArg (fun z => a ≫ z) (tensorHom_fst (f 0).hom.hom f')).trans
          (Category.assoc a (fst (B 0).X B'.X) (f 0).hom.hom).symm)
    · change Construction.groupBlockProductPointsEquiv n (fun w => C w.succ) T
        ((a ≫ ((f 0).hom.hom ⊗ₘ f')) ≫ snd (C 0).X C'.X) w = _
      have hp := (Category.assoc a ((f 0).hom.hom ⊗ₘ f') (snd (C 0).X C'.X)).trans
        ((congrArg (fun z => a ≫ z) (tensorHom_snd (f 0).hom.hom f')).trans
          (Category.assoc a (snd (B 0).X B'.X) f').symm)
      exact (congrArg (fun z => Construction.groupBlockProductPointsEquiv n (fun w => C w.succ) T z w) hp).trans
        (ih _ _ _ _ w)

end

end OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.ProductPoints.Construction

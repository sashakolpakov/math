import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Parameter.Products

/-! # Choices -/

namespace OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Universal.Choices.Construction

noncomputable section

/-!
Extract the universal chosen subgroups from the actual finite-product
parameter functor. The coordinate equivalence and its naturality identify
every family with the pullback of those universal subgroups.
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

variable {S : Scheme.{u}}

def blockTupleCoordinates : (s : ℕ) → (F : Fin s → (Over S)ᵒᵖ ⥤ Type (u + 1)) →
    (T : (Over S)ᵒᵖ) → (Parameter.Products.Construction.blockTupleFunctor s F).obj T ≃ (∀ i, (F i).obj T)
  | 0, _, _ => {
      toFun _ i := Fin.elim0 i
      invFun _ := PUnit.unit
      left_inv x := by
        change (PUnit.unit : PUnit.{u + 2}) = x
        cases x
        rfl
      right_inv _ := funext (fun i => Fin.elim0 i) }
  | s + 1, F, T => {
      toFun x := Fin.cons x.1 (blockTupleCoordinates s (fun i => F i.succ) T x.2)
      invFun x := (x 0, (blockTupleCoordinates s (fun i => F i.succ) T).symm (fun i => x i.succ))
      left_inv x := by
        cases x
        simp only [Fin.cons_zero, Fin.cons_succ, Equiv.symm_apply_apply]
        rfl
      right_inv x := by
        funext i
        refine Fin.cases ?_ (fun j => ?_) i
        · rfl
        · exact congrFun ((blockTupleCoordinates s (fun i => F i.succ) T).apply_symm_apply
            (fun i => x i.succ)) j }

theorem blockTupleCoordinates_natural
    (s : ℕ) (F : Fin s → (Over S)ᵒᵖ ⥤ Type (u + 1))
    {X Y : (Over S)ᵒᵖ} (f : X ⟶ Y) (x : (Parameter.Products.Construction.blockTupleFunctor s F).obj X) (i : Fin s) :
    Construction.blockTupleCoordinates s F Y ((Parameter.Products.Construction.blockTupleFunctor s F).map f x) i =
      (F i).map f (Construction.blockTupleCoordinates s F X x i) := by
  induction s with
  | zero => exact Fin.elim0 i
  | succ s ih =>
      refine Fin.cases ?_ (fun j => ?_) i
      · rfl
      · exact ih (fun i => F i.succ) x.2 j

/-- The universal tuple's coordinates pull back to each classified
family, via the supplied TorsionQuotient representation and its proved product. -/
theorem represented_block_coordinates
    (s : ℕ) (F : Fin s → (Over S)ᵒᵖ ⥤ Type (u + 1))
    {P T : Over S} (e : (Parameter.Products.Construction.blockTupleFunctor s F).RepresentableBy P) (b : T ⟶ P) (i : Fin s) :
    Construction.blockTupleCoordinates s F (.op T) (e.homEquiv b) i =
      (F i).map b.op (Construction.blockTupleCoordinates s F (.op P) (e.homEquiv (𝟙 P)) i) := by
  rw [e.homEquiv_eq]
  exact blockTupleCoordinates_natural s F b.op _ i

variable {A : Over S} [GrpObj A]
variable (n s : ℕ) (M : Fin s → Type u)
variable [∀ i, AddCommGroup (M i)] [∀ i, Module (ZMod n) (M i)] [∀ i, Finite (M i)]
variable (p : Fin s → (A ⟶ A))

def universalBlockChoice {P : Over S}
    (e : (Parameter.Products.Construction.blockTupleFunctor s (fun i => SubgroupFunctor.Construction.supportedSubgroupFunctor A n (M i) (p i))).RepresentableBy P)
    (i : Fin s) : SubgroupFunctor.Construction.SupportedChoice A n (M i) (p i) P :=
  Construction.blockTupleCoordinates s (fun i => SubgroupFunctor.Construction.supportedSubgroupFunctor A n (M i) (p i)) (.op P)
    (e.homEquiv (𝟙 P)) i

theorem universalBlockChoice_pullback {P T : Over S}
    (e : (Parameter.Products.Construction.blockTupleFunctor s (fun i => SubgroupFunctor.Construction.supportedSubgroupFunctor A n (M i) (p i))).RepresentableBy P)
    (b : T ⟶ P) (i : Fin s) :
    (Construction.blockTupleCoordinates s (fun i => SubgroupFunctor.Construction.supportedSubgroupFunctor A n (M i) (p i)) (.op T)
      (e.homEquiv b) i).val.subgroup =
        ((universalBlockChoice n s M p e i).val.subgroup).baseChange b := by
  have h := represented_block_coordinates s
    (fun i => SubgroupFunctor.Construction.supportedSubgroupFunctor A n (M i) (p i)) e b i
  exact congrArg (fun c : SubgroupFunctor.Construction.SupportedChoice A n (M i) (p i) T => c.val.subgroup) h

end

end OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Universal.Choices.Construction

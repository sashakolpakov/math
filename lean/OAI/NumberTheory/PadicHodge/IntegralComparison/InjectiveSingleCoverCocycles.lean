import OAI.NumberTheory.PadicHodge.IntegralComparison.InjectiveAbelianCechExactness

/-! # Injective Single Cover Cocycles -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.InjectiveSingleCoverCocycles

noncomputable section

/-! An additive cocycle on the overlap of a single covering object is
a difference of restrictions when its coefficient sheaf is injective. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits Opposite

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

universe u v
variable {C : Type (max u v)} [Category.{v} C] [HasBinaryProducts C] [HasTerminal C]
  (J : GrothendieckTopology C) (H : Sheaf J AddCommGrpCat.{max u v}) [Injective H]
  (U D : C) (a b : D ⟶ U)
  (hD : IsPullback a b (terminal.from U) (terminal.from U))

abbrev tuple (n : ℕ) : C := ∏ᶜ (fun _ : Fin (n + 1) => U)

def pair {V : C} (f g : V ⟶ U) : V ⟶ D :=
  hD.lift f g (by simp)

omit [HasBinaryProducts C] in
@[reassoc (attr := simp)] theorem pair_fst {V : C} (f g : V ⟶ U) :
    pair U D a b hD f g ≫ a = f := hD.lift_fst _ _ _

omit [HasBinaryProducts C] in
@[reassoc (attr := simp)] theorem pair_snd {V : C} (f g : V ⟶ U) :
    pair U D a b hD f g ≫ b = g := hD.lift_snd _ _ _

def overlapMap : tuple U 1 ⟶ D :=
  pair U D a b hD (Pi.π (fun _ : Fin 2 => U) 0) (Pi.π (fun _ : Fin 2 => U) 1)

omit [HasBinaryProducts C] [HasTerminal C] [Injective H] in
theorem restriction_comp {V W Z : C} (f : V ⟶ W) (g : W ⟶ Z) (x : H.obj.obj (op Z)) :
    H.obj.map f.op (H.obj.map g.op x) = H.obj.map (f ≫ g).op x := by
  rw [op_comp, Functor.map_comp]
  rfl

omit [HasBinaryProducts C] [HasTerminal C] [Injective H] in
theorem restriction_id {V : C} (x : H.obj.obj (op V)) : H.obj.map (𝟙 V).op x = x := by
  rw [op_id, CategoryTheory.Functor.map_id]
  rfl

include hD in
theorem primitive
    (hcover : ∀ V, CoveringObjectsSheafDetection.sieve (fun _ : PUnit.{v + 1} => U) V ∈ J V)
    (c : H.obj.obj (op D))
    (hc : ∀ (T : C) (p q r : T ⟶ D), p ≫ a = r ≫ a → p ≫ b = q ≫ a →
      q ≫ b = r ≫ b → H.obj.map p.op c + H.obj.map q.op c = H.obj.map r.op c) :
    ∃ t : H.obj.obj (op U), H.obj.map a.op t - H.obj.map b.op t = c := by
  let F := fun _ : PUnit.{v + 1} => U
  let π (i : Fin 3) := Pi.π (fun _ : Fin 3 => U) i
  let p := pair U D a b hD (π 0) (π 1)
  let q := pair U D a b hD (π 1) (π 2)
  let r := pair U D a b hD (π 0) (π 2)
  have hc' := hc (tuple U 2) p q r
    ((pair_fst U D a b hD _ _).trans (pair_fst U D a b hD _ _).symm)
    ((pair_snd U D a b hD _ _).trans (pair_fst U D a b hD _ _).symm)
    ((pair_snd U D a b hD _ _).trans (pair_snd U D a b hD _ _).symm)
  let x : ∀ t : Fin 2 → PUnit.{v + 1},
      H.obj.obj (op (Presentation.TupleProducts.family F 1 t)) :=
    fun _ => H.obj.map (overlapMap U D a b hD).op c
  have hx : ∀ t : Fin 3 → PUnit.{v + 1},
      (∑ i : Fin 3, (-1 : ℤ) ^ (i : ℕ) •
        H.obj.map (Presentation.ResolutionFaceMaps.productMap F i.succAbove t).op
          (x (t ∘ i.succAbove))) = 0 := by
    intro t
    have he (i : Fin 3) :
        Presentation.ResolutionFaceMaps.productMap F i.succAbove t ≫
          overlapMap U D a b hD =
            pair U D a b hD (π (i.succAbove 0)) (π (i.succAbove 1)) := by
      apply hD.hom_ext
      · simp [overlapMap, Presentation.ResolutionFaceMaps.productMap, π, F]
      · simp [overlapMap, Presentation.ResolutionFaceMaps.productMap, π, F]
    have ht (i : Fin 3) :
        H.obj.map (Presentation.ResolutionFaceMaps.productMap F i.succAbove t).op
          (x (t ∘ i.succAbove)) =
        H.obj.map (pair U D a b hD (π (i.succAbove 0)) (π (i.succAbove 1))).op c := by
      exact (restriction_comp J H _ _ c).trans
        (congrArg (fun f => H.obj.map f.op c) (he i))
    simp only [ht]
    simp only [Fin.sum_univ_three, Fin.val_zero, pow_zero, one_zsmul, Fin.val_one, pow_one,
      neg_one_zsmul, Fin.val_two, neg_one_sq]
    change H.obj.map q.op c + -H.obj.map r.op c + H.obj.map p.op c = 0
    rw [← hc']
    abel
  obtain ⟨y, hy⟩ := InjectiveAbelianCechExactness.boundary F J H hcover 0 x hx
  let t₀ : Fin 1 → PUnit.{v + 1} := fun _ => PUnit.unit
  let t₁ : Fin 2 → PUnit.{v + 1} := fun _ => PUnit.unit
  change (Fin 1 → PUnit.{v + 1}) → H.obj.obj (op (tuple U 0)) at y
  let z := y t₀
  let s : U ⟶ tuple U 0 := Pi.lift (fun _ => 𝟙 U)
  let e : D ⟶ tuple U 1 := Pi.lift (fun i : Fin 2 => if i = 0 then a else b)
  have he₀ : e ≫ Pi.π (fun _ : Fin 2 => U) 0 = a := by simp [e]
  have he₁ : e ≫ Pi.π (fun _ : Fin 2 => U) 1 = b := by simp [e]
  have hec : e ≫ overlapMap U D a b hD = 𝟙 D := by
    apply hD.hom_ext <;> simp [overlapMap, he₀, he₁]
  have heface (i : Fin 2) :
      e ≫ Presentation.ResolutionFaceMaps.productMap F i.succAbove t₁ =
        (if i = 0 then b else a) ≫ s := by
    apply Pi.hom_ext
    intro j
    fin_cases j
    fin_cases i <;> simp [Presentation.ResolutionFaceMaps.productMap, s, F, he₀, he₁, Category.assoc]
  have hy' := hy t₁
  have hyval (t : Fin 1 → PUnit.{v + 1}) : y t = z :=
    congrArg y (Subsingleton.elim t t₀)
  simp only [Nat.reduceAdd, hyval, Fin.sum_univ_two, Fin.val_zero, pow_zero, one_zsmul,
    Fin.val_one, pow_one, neg_one_zsmul] at hy'
  have hv := congrArg (H.obj.map e.op) hy'
  have hev (i : Fin 2) :
      H.obj.map e.op
        (H.obj.map (Presentation.ResolutionFaceMaps.productMap F i.succAbove t₁).op z) =
      H.obj.map (if i = 0 then b else a).op (H.obj.map s.op z) := by
    exact (restriction_comp J H _ _ z).trans
      ((congrArg (fun f => H.obj.map f.op z) (heface i)).trans
        (restriction_comp J H _ _ z).symm)
  have hexc : H.obj.map e.op (x t₁) = c :=
    (restriction_comp J H _ _ c).trans
      ((congrArg (fun f => H.obj.map f.op c) hec).trans (restriction_id J H c))
  simp only [map_add, map_neg, hev, hexc] at hv
  refine ⟨-H.obj.map s.op z, ?_⟩
  simp only [map_neg, sub_neg_eq_add]
  have hv' : H.obj.map b.op (H.obj.map s.op z) +
      -H.obj.map a.op (H.obj.map s.op z) = c := hv
  exact (add_comm _ _).trans hv'

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.InjectiveSingleCoverCocycles

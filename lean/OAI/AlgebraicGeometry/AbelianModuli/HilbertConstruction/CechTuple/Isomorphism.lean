import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.IntrinsicCech.Differential

/-! # Isomorphism -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.CechTuple.Isomorphism

noncomputable section

/-! Isomorphisms on the actual tuple intersections, compatible with tuple-deletion restrictions, induce an isomorphism of native Cech complexes. -/
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.TopologicalSpace Opposite
universe u

variable {X : TopCat.{u}} {F G : (Opens X)ᵒᵖ ⥤ AddCommGrpCat.{u}}
variable {ι : Type u} (U : ι → Opens X)
variable (e : ∀ (n : ℕ) (i : Fin (n + 1) → ι),
  F.obj (op (∏ᶜ fun k => U (i k))) ≅ G.obj (op (∏ᶜ fun k => U (i k))))
variable (h : ∀ (n : ℕ) (k : Fin (n + 2)) (i : Fin (n + 2) → ι),
  F.map (((FormalCoproduct.mk _ U).mapPower (SimplexCategory.δ k).toOrderHom.toFun).φ i).op ≫
      (e (n + 1) i).hom =
    (e n (i ∘ (SimplexCategory.δ k).toOrderHom.toFun)).hom ≫
      G.map (((FormalCoproduct.mk _ U).mapPower (SimplexCategory.δ k).toOrderHom.toFun).φ i).op)

def cechTupleObjectIso (n : ℕ) :
    ((cechComplexFunctor U).obj F).X n ≅ ((cechComplexFunctor U).obj G).X n :=
  Pi.mapIso (e n)

include h in
theorem cechTupleObjectIso_coface (n : ℕ) (k : Fin (n + 2)) :
    ((FormalCoproduct.cosimplicialObjectFunctor (FormalCoproduct.mk _ U).cech).obj F).δ k ≫
        (cechTupleObjectIso U e (n + 1)).hom =
      (cechTupleObjectIso U e n).hom ≫
        ((FormalCoproduct.cosimplicialObjectFunctor (FormalCoproduct.mk _ U).cech).obj G).δ k := by
  let S (q : ℕ) := ∏ᶜ fun j : Fin (q + 1) → ι => F.obj (op (∏ᶜ fun l => U (j l)))
  let T (q : ℕ) := ∏ᶜ fun j : Fin (q + 1) → ι => G.obj (op (∏ᶜ fun l => U (j l)))
  let δF : S n ⟶ S (n + 1) :=
    ((FormalCoproduct.cosimplicialObjectFunctor (FormalCoproduct.mk _ U).cech).obj F).δ k
  let δG : T n ⟶ T (n + 1) :=
    ((FormalCoproduct.cosimplicialObjectFunctor (FormalCoproduct.mk _ U).cech).obj G).δ k
  change δF ≫ (cechTupleObjectIso U e (n + 1)).hom = (cechTupleObjectIso U e n).hom ≫ δG
  apply Pi.hom_ext
  intro i
  change Fin (n + 2) → ι at i
  let i' : Fin (n + 1) → ι := i ∘ (SimplexCategory.δ k).toOrderHom.toFun
  let q : op (∏ᶜ fun l => U (i' l)) ⟶ op (∏ᶜ fun l => U (i l)) :=
    (((FormalCoproduct.mk _ U).mapPower (SimplexCategory.δ k).toOrderHom.toFun).φ i).op
  let pF := Pi.π (fun j : Fin (n + 1) → ι => F.obj (op (∏ᶜ fun l => U (j l)))) i'
  let pF' := Pi.π (fun j : Fin (n + 2) → ι => F.obj (op (∏ᶜ fun l => U (j l)))) i
  let pG := Pi.π (fun j : Fin (n + 1) → ι => G.obj (op (∏ᶜ fun l => U (j l)))) i'
  let pG' := Pi.π (fun j : Fin (n + 2) → ι => G.obj (op (∏ᶜ fun l => U (j l)))) i
  have hF : δF ≫ pF' = pF ≫ F.map q :=
    (congrArg (fun d : S n ⟶ S (n + 1) => d ≫ pF')
      (IntrinsicCech.Cofaces.cechCoface_eq F U n k)).trans (Pi.lift_comp_π _ i)
  have hG : δG ≫ pG' = pG ≫ G.map q :=
    (congrArg (fun d : T n ⟶ T (n + 1) => d ≫ pG')
      (IntrinsicCech.Cofaces.cechCoface_eq G U n k)).trans (Pi.lift_comp_π _ i)
  have hq : F.map q ≫ (e (n + 1) i).hom = (e n i').hom ≫ G.map q := h n k i
  change (δF ≫ (Pi.mapIso (e (n + 1))).hom) ≫ pG' =
    ((Pi.mapIso (e n)).hom ≫ δG) ≫ pG'
  calc
    _ = δF ≫ (pF' ≫ (e (n + 1) i).hom) := by rw [Category.assoc, Pi.mapIso_hom_π]
    _ = (pF ≫ F.map q) ≫ (e (n + 1) i).hom := by rw [← Category.assoc, hF]
    _ = pF ≫ ((e n i').hom ≫ G.map q) := by rw [Category.assoc, hq]
    _ = ((Pi.mapIso (e n)).hom ≫ pG) ≫ G.map q := by rw [← Category.assoc, Pi.mapIso_hom_π]
    _ = _ := by simpa only [Category.assoc] using congrArg (fun z => (Pi.mapIso (e n)).hom ≫ z) hG.symm

include h in
theorem cechTupleObjectIso_differential (n : ℕ) :
    ((cechComplexFunctor U).obj F).d n (n + 1) ≫ (cechTupleObjectIso U e (n + 1)).hom =
      (cechTupleObjectIso U e n).hom ≫ ((cechComplexFunctor U).obj G).d n (n + 1) := by
  let δF (k : Fin (n + 2)) : ((cechComplexFunctor U).obj F).X n ⟶
      ((cechComplexFunctor U).obj F).X (n + 1) :=
    ((FormalCoproduct.cosimplicialObjectFunctor (FormalCoproduct.mk _ U).cech).obj F).δ k
  let δG (k : Fin (n + 2)) : ((cechComplexFunctor U).obj G).X n ⟶
      ((cechComplexFunctor U).obj G).X (n + 1) :=
    ((FormalCoproduct.cosimplicialObjectFunctor (FormalCoproduct.mk _ U).cech).obj G).δ k
  have hF : ((cechComplexFunctor U).obj F).d n (n + 1) =
      ∑ k : Fin (n + 2), (-1 : ℤ) ^ (k : ℕ) • δF k := IntrinsicCech.Cofaces.cechDifferential_eq F U n
  have hG : ((cechComplexFunctor U).obj G).d n (n + 1) =
      ∑ k : Fin (n + 2), (-1 : ℤ) ^ (k : ℕ) • δG k := IntrinsicCech.Cofaces.cechDifferential_eq G U n
  rw [hF, hG]
  simp only [Preadditive.sum_comp, Preadditive.comp_sum, Preadditive.zsmul_comp, Preadditive.comp_zsmul]
  apply Finset.sum_congr rfl
  intro k _
  exact congrArg ((-1 : ℤ) ^ (k : ℕ) • ·) (cechTupleObjectIso_coface U e h n k)

include h in
def cechComplexIsoOfTupleIsos : (cechComplexFunctor U).obj F ≅ (cechComplexFunctor U).obj G :=
  HomologicalComplex.Hom.isoOfComponents (fun n => cechTupleObjectIso U e n) (by
    intro i j hij
    simp only [ComplexShape.up_Rel] at hij
    subst j
    exact (cechTupleObjectIso_differential U e h i).symm)

theorem additiveCochain_firstDifferential_injective_of_iso
    {C D : CochainComplex AddCommGrpCat.{u} ℕ} (e : C ≅ D)
    (hC : Function.Injective (C.d 0 1)) : Function.Injective (D.d 0 1) := by
  have hi : Function.Injective (e.inv.f 0) :=
    (AddCommGrpCat.mono_iff_injective (e.inv.f 0)).mp inferInstance
  intro x y hxy
  apply hi
  apply hC
  exact (ConcreteCategory.congr_hom (e.inv.comm 0 1) x).trans
    ((congrArg (e.inv.f 1) hxy).trans (ConcreteCategory.congr_hom (e.inv.comm 0 1) y).symm)

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.CechTuple.Isomorphism

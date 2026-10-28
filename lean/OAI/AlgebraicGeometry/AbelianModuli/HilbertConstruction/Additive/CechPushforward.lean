import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.IntrinsicCech.Differential
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.CoefficientCech.PushforwardFactors

/-! # Cech Pushforward -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Additive.CechPushforward

noncomputable section

/-! The native additive Cech complex on an inverse-image cover agrees with the Cech complex of the direct-image presheaf. This comparison only uses the actual equality of intersection opens. -/
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.TopologicalSpace _root_.AlgebraicGeometry Opposite
universe u

variable {X P : Scheme.{u}} (a : P ⟶ X) (F : P.Opensᵒᵖ ⥤ AddCommGrpCat.{u})
variable {ι : Type u} (U : ι → X.Opens)

def additiveCechPushforwardFactorIso (n : ℕ) (i : Fin (n + 1) → ι) :
    F.obj (op (∏ᶜ fun k : Fin (n + 1) => a ⁻¹ᵁ U (i k))) ≅
      F.obj (op (a ⁻¹ᵁ (∏ᶜ fun k : Fin (n + 1) => U (i k)))) :=
  F.mapIso (eqToIso (CoefficientCech.PushforwardFactors.preimageCechIntersection a U n i)).op

def additiveCechPushforwardObjectIso (n : ℕ) :
    ((cechComplexFunctor (fun i => a ⁻¹ᵁ U i)).obj F).X n ≅
      ((cechComplexFunctor U).obj ((Opens.map a.base).op ⋙ F)).X n :=
  Pi.mapIso (fun i : Fin (n + 1) → ι => additiveCechPushforwardFactorIso a F U n i)

@[reassoc]
theorem additiveCechPushforwardObjectIso_hom_π (n : ℕ) (i : Fin (n + 1) → ι) :
    (additiveCechPushforwardObjectIso a F U n).hom ≫
      Pi.π (fun j : Fin (n + 1) → ι => F.obj (op (a ⁻¹ᵁ (∏ᶜ fun k => U (j k))))) i =
    Pi.π (fun j : Fin (n + 1) → ι => F.obj (op (∏ᶜ fun k => a ⁻¹ᵁ U (j k)))) i ≫
      (additiveCechPushforwardFactorIso a F U n i).hom :=
  Pi.mapIso_hom_π _ i

theorem additiveCechPushforwardFactorIso_coface (n : ℕ) (k : Fin (n + 2))
    (i : Fin (n + 2) → ι) :
    F.map (((FormalCoproduct.mk _ (fun j => a ⁻¹ᵁ U j)).mapPower
      (SimplexCategory.δ k).toOrderHom.toFun).φ i).op ≫
        (additiveCechPushforwardFactorIso a F U (n + 1) i).hom =
      (additiveCechPushforwardFactorIso a F U n
        (i ∘ (SimplexCategory.δ k).toOrderHom.toFun)).hom ≫
          F.map ((Opens.map a.base).map
            (((FormalCoproduct.mk _ U).mapPower (SimplexCategory.δ k).toOrderHom.toFun).φ i)).op := by
  let i' : Fin (n + 1) → ι := i ∘ (SimplexCategory.δ k).toOrderHom.toFun
  let rs : (∏ᶜ fun l => a ⁻¹ᵁ U (i l)) ⟶ (∏ᶜ fun l => a ⁻¹ᵁ U (i' l)) :=
    ((FormalCoproduct.mk _ (fun j => a ⁻¹ᵁ U j)).mapPower (SimplexCategory.δ k).toOrderHom.toFun).φ i
  let rt : (a ⁻¹ᵁ ∏ᶜ fun l => U (i l)) ⟶ (a ⁻¹ᵁ ∏ᶜ fun l => U (i' l)) :=
    (Opens.map a.base).map (((FormalCoproduct.mk _ U).mapPower (SimplexCategory.δ k).toOrderHom.toFun).φ i)
  let q₀ : op (∏ᶜ fun l => a ⁻¹ᵁ U (i' l)) ⟶ op (a ⁻¹ᵁ ∏ᶜ fun l => U (i' l)) :=
    (eqToIso (CoefficientCech.PushforwardFactors.preimageCechIntersection a U n i')).op.hom
  let q₁ : op (∏ᶜ fun l => a ⁻¹ᵁ U (i l)) ⟶ op (a ⁻¹ᵁ ∏ᶜ fun l => U (i l)) :=
    (eqToIso (CoefficientCech.PushforwardFactors.preimageCechIntersection a U (n + 1) i)).op.hom
  change F.map rs.op ≫ F.map q₁ = F.map q₀ ≫ F.map rt.op
  rw [← F.map_comp, ← F.map_comp]
  exact F.congr_map (Subsingleton.elim _ _)

theorem additiveCechPushforwardObjectIso_coface (n : ℕ) (k : Fin (n + 2)) :
    ((FormalCoproduct.cosimplicialObjectFunctor
      (FormalCoproduct.mk _ (fun i => a ⁻¹ᵁ U i)).cech).obj F).δ k ≫
        (additiveCechPushforwardObjectIso a F U (n + 1)).hom =
      (additiveCechPushforwardObjectIso a F U n).hom ≫
        ((FormalCoproduct.cosimplicialObjectFunctor (FormalCoproduct.mk _ U).cech).obj
          ((Opens.map a.base).op ⋙ F)).δ k := by
  let S (q : ℕ) := ∏ᶜ fun j : Fin (q + 1) → ι => F.obj (op (∏ᶜ fun l => a ⁻¹ᵁ U (j l)))
  let T (q : ℕ) := ∏ᶜ fun j : Fin (q + 1) → ι => F.obj (op (a ⁻¹ᵁ (∏ᶜ fun l => U (j l))))
  let δs : S n ⟶ S (n + 1) := ((FormalCoproduct.cosimplicialObjectFunctor
    (FormalCoproduct.mk _ (fun i => a ⁻¹ᵁ U i)).cech).obj F).δ k
  let δt : T n ⟶ T (n + 1) :=
    ((FormalCoproduct.cosimplicialObjectFunctor (FormalCoproduct.mk _ U).cech).obj
      ((Opens.map a.base).op ⋙ F)).δ k
  let e₀ : S n ≅ T n := additiveCechPushforwardObjectIso a F U n
  let e₁ : S (n + 1) ≅ T (n + 1) := additiveCechPushforwardObjectIso a F U (n + 1)
  change δs ≫ e₁.hom = e₀.hom ≫ δt
  apply Pi.hom_ext
  intro i
  change Fin (n + 2) → ι at i
  let i' : Fin (n + 1) → ι := i ∘ (SimplexCategory.δ k).toOrderHom.toFun
  let ps := Pi.π (fun j : Fin (n + 1) → ι => F.obj (op (∏ᶜ fun l => a ⁻¹ᵁ U (j l)))) i'
  let ps' := Pi.π (fun j : Fin (n + 2) → ι => F.obj (op (∏ᶜ fun l => a ⁻¹ᵁ U (j l)))) i
  let pt := Pi.π (fun j : Fin (n + 1) → ι => F.obj (op (a ⁻¹ᵁ (∏ᶜ fun l => U (j l))))) i'
  let pt' := Pi.π (fun j : Fin (n + 2) → ι => F.obj (op (a ⁻¹ᵁ (∏ᶜ fun l => U (j l))))) i
  let rs : (∏ᶜ fun l => a ⁻¹ᵁ U (i l)) ⟶ (∏ᶜ fun l => a ⁻¹ᵁ U (i' l)) :=
    ((FormalCoproduct.mk _ (fun j => a ⁻¹ᵁ U j)).mapPower (SimplexCategory.δ k).toOrderHom.toFun).φ i
  let rt : (a ⁻¹ᵁ ∏ᶜ fun l => U (i l)) ⟶ (a ⁻¹ᵁ ∏ᶜ fun l => U (i' l)) :=
    (Opens.map a.base).map (((FormalCoproduct.mk _ U).mapPower (SimplexCategory.δ k).toOrderHom.toFun).φ i)
  have hs : δs ≫ ps' = ps ≫ F.map rs.op :=
    (congrArg (fun d : S n ⟶ S (n + 1) => d ≫ ps')
      (IntrinsicCech.Cofaces.cechCoface_eq F (fun i => a ⁻¹ᵁ U i) n k)).trans (Pi.lift_comp_π _ i)
  have ht : δt ≫ pt' = pt ≫ F.map rt.op :=
    (congrArg (fun d : T n ⟶ T (n + 1) => d ≫ pt')
      (IntrinsicCech.Cofaces.cechCoface_eq ((Opens.map a.base).op ⋙ F) U n k)).trans (Pi.lift_comp_π _ i)
  have hr : F.map rs.op ≫ (additiveCechPushforwardFactorIso a F U (n + 1) i).hom =
      (additiveCechPushforwardFactorIso a F U n i').hom ≫ F.map rt.op :=
    additiveCechPushforwardFactorIso_coface a F U n k i
  have he₀ : e₀.hom ≫ pt = ps ≫ (additiveCechPushforwardFactorIso a F U n i').hom :=
    additiveCechPushforwardObjectIso_hom_π a F U n i'
  have he₁ : e₁.hom ≫ pt' = ps' ≫ (additiveCechPushforwardFactorIso a F U (n + 1) i).hom :=
    additiveCechPushforwardObjectIso_hom_π a F U (n + 1) i
  change (δs ≫ e₁.hom) ≫ pt' = (e₀.hom ≫ δt) ≫ pt'
  calc
    _ = δs ≫ (ps' ≫ (additiveCechPushforwardFactorIso a F U (n + 1) i).hom) := by
      rw [Category.assoc, he₁]
    _ = (ps ≫ F.map rs.op) ≫ (additiveCechPushforwardFactorIso a F U (n + 1) i).hom := by
      rw [← Category.assoc, hs]
    _ = ps ≫ ((additiveCechPushforwardFactorIso a F U n i').hom ≫ F.map rt.op) := by
      rw [Category.assoc, hr]
    _ = (e₀.hom ≫ pt) ≫ F.map rt.op := by
      rw [← Category.assoc, he₀]
    _ = _ := by simpa only [Category.assoc] using congrArg (fun z => e₀.hom ≫ z) ht.symm

theorem additiveCechPushforwardObjectIso_differential (n : ℕ) :
    ((cechComplexFunctor (fun i => a ⁻¹ᵁ U i)).obj F).d n (n + 1) ≫
        (additiveCechPushforwardObjectIso a F U (n + 1)).hom =
      (additiveCechPushforwardObjectIso a F U n).hom ≫
        ((cechComplexFunctor U).obj ((Opens.map a.base).op ⋙ F)).d n (n + 1) := by
  let Cs := (cechComplexFunctor (fun i => a ⁻¹ᵁ U i)).obj F
  let Ct := (cechComplexFunctor U).obj ((Opens.map a.base).op ⋙ F)
  let δs (k : Fin (n + 2)) : Cs.X n ⟶ Cs.X (n + 1) :=
    ((FormalCoproduct.cosimplicialObjectFunctor
      (FormalCoproduct.mk _ (fun i => a ⁻¹ᵁ U i)).cech).obj F).δ k
  let δt (k : Fin (n + 2)) : Ct.X n ⟶ Ct.X (n + 1) :=
    ((FormalCoproduct.cosimplicialObjectFunctor (FormalCoproduct.mk _ U).cech).obj
      ((Opens.map a.base).op ⋙ F)).δ k
  have hs : Cs.d n (n + 1) = ∑ k : Fin (n + 2), (-1 : ℤ) ^ (k : ℕ) • δs k :=
    IntrinsicCech.Cofaces.cechDifferential_eq F (fun i => a ⁻¹ᵁ U i) n
  have ht : Ct.d n (n + 1) = ∑ k : Fin (n + 2), (-1 : ℤ) ^ (k : ℕ) • δt k :=
    IntrinsicCech.Cofaces.cechDifferential_eq ((Opens.map a.base).op ⋙ F) U n
  change Cs.d n (n + 1) ≫ (additiveCechPushforwardObjectIso a F U (n + 1)).hom =
    (additiveCechPushforwardObjectIso a F U n).hom ≫ Ct.d n (n + 1)
  rw [hs, ht]
  simp only [Preadditive.sum_comp, Preadditive.comp_sum,
    Preadditive.zsmul_comp, Preadditive.comp_zsmul]
  apply Finset.sum_congr rfl
  intro k _
  exact congrArg ((-1 : ℤ) ^ (k : ℕ) • ·) (additiveCechPushforwardObjectIso_coface a F U n k)

def additiveCechPushforwardComplexIso :
    (cechComplexFunctor (fun i => a ⁻¹ᵁ U i)).obj F ≅
      (cechComplexFunctor U).obj ((Opens.map a.base).op ⋙ F) :=
  HomologicalComplex.Hom.isoOfComponents (fun n => additiveCechPushforwardObjectIso a F U n) (by
    intro i j hij
    simp only [ComplexShape.up_Rel] at hij
    subst j
    exact (additiveCechPushforwardObjectIso_differential a F U i).symm)

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Additive.CechPushforward

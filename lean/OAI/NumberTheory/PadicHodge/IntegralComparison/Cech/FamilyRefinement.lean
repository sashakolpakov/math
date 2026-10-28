import OAI.NumberTheory.PadicHodge.IntegralComparison.Frame.CosimplicialRefinement
import OAI.NumberTheory.PadicHodge.IntegralComparison.Frame.TupleRefinement

/-! # Family Refinement -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Cech.FamilyRefinement.Family

noncomputable section

/-! Refining an actual frame family gives a native cosimplicial coefficient
map for any presheaf, including the original coefficient algebra presheaf. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits Opposite

universe u v t s

variable {C : Type (max u v)} [Category.{v} C] [HasBinaryProducts C]
  {ι κ : Type v} (F : ι → C) (G : κ → C) (ρ : ι → κ)
  (α : ∀ i, F i ⟶ G (ρ i))
  {A : Type t} [Category.{s} A] [HasProducts.{v} A] (H : Cᵒᵖ ⥤ A)

def coefficient (a : ℕ) (t : Fin (a + 1) → ι) :=
  H.map (Frame.TupleRefinement.map (𝟭 C) F G ρ α a t).op

omit [HasProducts A] in
theorem coefficient_naturality (a b : ℕ) (θ : Fin (b + 1) → Fin (a + 1)) (t : Fin (a + 1) → ι) :
    coefficient F G ρ α H b (t ∘ θ) ≫ H.map (Presentation.ResolutionFaceMaps.productMap F θ t).op =
      H.map (Presentation.ResolutionFaceMaps.productMap G θ (ρ ∘ t)).op ≫ coefficient F G ρ α H a t :=
  (H.map_comp (Frame.TupleRefinement.map (𝟭 C) F G ρ α b (t ∘ θ)).op
    (Presentation.ResolutionFaceMaps.productMap F θ t).op).symm.trans
    ((congrArg (fun z => H.map z.op) (Frame.TupleRefinement.naturality (𝟭 C) F G ρ α a b θ t)).trans
      (H.map_comp (Presentation.ResolutionFaceMaps.productMap G θ (ρ ∘ t)).op
        (Frame.TupleRefinement.map (𝟭 C) F G ρ α a t).op))

def map :
    (FormalCoproduct.cosimplicialObjectFunctor (NonemptyCechNerve.nerve G)).obj H ⟶
      (FormalCoproduct.cosimplicialObjectFunctor (NonemptyCechNerve.nerve F)).obj H :=
  Frame.CosimplicialRefinement.map G F ρ H H
    (coefficient F G ρ α H) (coefficient_naturality F G ρ α H)

variable (K : Cᵒᵖ ⥤ A) (μ : H ⟶ K)

theorem naturality :
    (FormalCoproduct.cosimplicialObjectFunctor (NonemptyCechNerve.nerve G)).map μ ≫
      Family.map F G ρ α K = Family.map F G ρ α H ≫
        (FormalCoproduct.cosimplicialObjectFunctor (NonemptyCechNerve.nerve F)).map μ := by
  apply NatTrans.ext
  funext a
  let HG := fun t => H.obj (op (Presentation.TupleProducts.family G a.len t))
  let KG := fun t => K.obj (op (Presentation.TupleProducts.family G a.len t))
  let HF := fun t => H.obj (op (Presentation.TupleProducts.family F a.len t))
  let KF := fun t => K.obj (op (Presentation.TupleProducts.family F a.len t))
  let μG := Limits.Pi.map (fun t => μ.app (op (Presentation.TupleProducts.family G a.len t)))
  let μF := Limits.Pi.map (fun t => μ.app (op (Presentation.TupleProducts.family F a.len t)))
  let cH := (Family.map F G ρ α H).app a
  let cK := (Family.map F G ρ α K).app a
  apply Pi.hom_ext
  intro t
  let U := op (Presentation.TupleProducts.family F a.len t)
  let V := op (Presentation.TupleProducts.family G a.len (ρ ∘ t))
  let b := (Frame.TupleRefinement.map (𝟭 C) F G ρ α a.len t).op
  have hG : μG ≫ Pi.π KG (ρ ∘ t) = Pi.π HG (ρ ∘ t) ≫ μ.app V := Pi.map_π _ _
  have hF : μF ≫ Pi.π KF t = Pi.π HF t ≫ μ.app U := Pi.map_π _ _
  have hH : cH ≫ Pi.π HF t = Pi.π HG (ρ ∘ t) ≫ H.map b := Pi.lift_comp_π _ _
  have hK : cK ≫ Pi.π KF t = Pi.π KG (ρ ∘ t) ≫ K.map b := Pi.lift_comp_π _ _
  have hl : (μG ≫ cK) ≫ Pi.π KF t = Pi.π HG (ρ ∘ t) ≫ (μ.app V ≫ K.map b) :=
    (Category.assoc _ _ _).trans
      ((congrArg (fun z => μG ≫ z) hK).trans
        ((Category.assoc _ _ _).symm.trans
          ((congrArg (fun z => z ≫ K.map b) hG).trans (Category.assoc _ _ _))))
  have hr : (cH ≫ μF) ≫ Pi.π KF t = Pi.π HG (ρ ∘ t) ≫ (H.map b ≫ μ.app U) :=
    (Category.assoc _ _ _).trans
      ((congrArg (fun z => cH ≫ z) hF).trans
        ((Category.assoc _ _ _).symm.trans
          ((congrArg (fun z => z ≫ μ.app U) hH).trans (Category.assoc _ _ _))))
  exact hl.trans ((congrArg (fun z => Pi.π HG (ρ ∘ t) ≫ z) (μ.naturality b).symm).trans hr.symm)

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Cech.FamilyRefinement.Family

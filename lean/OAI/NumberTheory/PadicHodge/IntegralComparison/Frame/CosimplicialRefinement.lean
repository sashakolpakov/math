import OAI.NumberTheory.PadicHodge.IntegralComparison.Frame.CosimplicialTransformation

/-! # Cosimplicial Refinement -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Frame.CosimplicialRefinement

noncomputable section

/-! Actual maps of tuple coefficients along a refinement of the frame index
set induce a map before forgetting the coefficient algebra structure. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits Opposite Simplicial

universe u v t s

variable {C D : Type (max u v)} [Category.{v} C] [Category.{v} D]
  [HasBinaryProducts C] [HasBinaryProducts D] {ι κ : Type v}
  (F : ι → C) (G : κ → D) (ρ : κ → ι)
  {A : Type t} [Category.{s} A] [HasProducts.{v} A]
  (H : Cᵒᵖ ⥤ A) (J : Dᵒᵖ ⥤ A)
  (c : ∀ (a : ℕ) (t : Fin (a + 1) → κ),
    H.obj (op (Presentation.TupleProducts.family F a (ρ ∘ t))) ⟶
      J.obj (op (Presentation.TupleProducts.family G a t)))
  (hc : ∀ (a b : ℕ) (θ : Fin (b + 1) → Fin (a + 1)) (t : Fin (a + 1) → κ),
    c b (t ∘ θ) ≫ J.map (Presentation.ResolutionFaceMaps.productMap G θ t).op =
      H.map (Presentation.ResolutionFaceMaps.productMap F θ (ρ ∘ t)).op ≫ c a t)

def component (a : ℕ) :
    ∏ᶜ (fun t => H.obj (op (Presentation.TupleProducts.family F a t))) ⟶
      ∏ᶜ (fun t => J.obj (op (Presentation.TupleProducts.family G a t))) :=
  Pi.lift (fun t => Pi.π (fun t => H.obj (op (Presentation.TupleProducts.family F a t)))
    (ρ ∘ t) ≫ c a t)

def map :
    (FormalCoproduct.cosimplicialObjectFunctor (NonemptyCechNerve.nerve F)).obj H ⟶
      (FormalCoproduct.cosimplicialObjectFunctor (NonemptyCechNerve.nerve G)).obj J where
  app a := component F G ρ H J c a.len
  naturality {a b} θ := by
    let Hₐ := fun t => H.obj (op (Presentation.TupleProducts.family F a.len t))
    let Hᵦ := fun t => H.obj (op (Presentation.TupleProducts.family F b.len t))
    let Jₐ := fun t => J.obj (op (Presentation.TupleProducts.family G a.len t))
    let Jᵦ := fun t => J.obj (op (Presentation.TupleProducts.family G b.len t))
    let α := ((FormalCoproduct.cosimplicialObjectFunctor (NonemptyCechNerve.nerve F)).obj H).map θ
    let β := ((FormalCoproduct.cosimplicialObjectFunctor (NonemptyCechNerve.nerve G)).obj J).map θ
    let cₐ := component F G ρ H J c a.len
    let cᵦ := component F G ρ H J c b.len
    apply Pi.hom_ext
    intro t
    let s := t ∘ θ.toOrderHom.toFun
    let h := H.map (Presentation.ResolutionFaceMaps.productMap F θ.toOrderHom.toFun (ρ ∘ t)).op
    let j := J.map (Presentation.ResolutionFaceMaps.productMap G θ.toOrderHom.toFun t).op
    have hα : α ≫ Pi.π Hᵦ (ρ ∘ t) = Pi.π Hₐ (ρ ∘ s) ≫ h := Pi.lift_comp_π _ (ρ ∘ t)
    have hβ : β ≫ Pi.π Jᵦ t = Pi.π Jₐ s ≫ j := Pi.lift_comp_π _ t
    have ha : cₐ ≫ Pi.π Jₐ s = Pi.π Hₐ (ρ ∘ s) ≫ c a.len s := Pi.lift_comp_π _ s
    have hb : cᵦ ≫ Pi.π Jᵦ t = Pi.π Hᵦ (ρ ∘ t) ≫ c b.len t := Pi.lift_comp_π _ t
    have hleft : (α ≫ cᵦ) ≫ Pi.π Jᵦ t = Pi.π Hₐ (ρ ∘ s) ≫ (h ≫ c b.len t) :=
      (Category.assoc _ _ _).trans
        ((congrArg (fun q => α ≫ q) hb).trans
          ((Category.assoc _ _ _).symm.trans
            ((congrArg (fun q => q ≫ c b.len t) hα).trans (Category.assoc _ _ _))))
    have hright : (cₐ ≫ β) ≫ Pi.π Jᵦ t = Pi.π Hₐ (ρ ∘ s) ≫ (c a.len s ≫ j) :=
      (Category.assoc _ _ _).trans
        ((congrArg (fun q => cₐ ≫ q) hβ).trans
          ((Category.assoc _ _ _).symm.trans
            ((congrArg (fun q => q ≫ j) ha).trans (Category.assoc _ _ _))))
    exact hleft.trans ((congrArg (fun q => Pi.π Hₐ (ρ ∘ s) ≫ q)
      (hc b.len a.len θ.toOrderHom.toFun t).symm).trans hright.symm)

variable {B : Type t} [Category.{s} B] [HasProducts.{v} B]
  (T : A ⥤ B) [PreservesLimitsOfSize.{v, v} T]

omit [HasBinaryProducts C] [HasBinaryProducts D] [PreservesLimitsOfSize.{v, v} T] in
theorem piComparison_reindex {P : ι → A} {Q : κ → A} (c : ∀ t, P (ρ t) ⟶ Q t) :
    T.map (Pi.lift (fun t => Pi.π P (ρ t) ≫ c t)) ≫ piComparison T Q =
      piComparison T P ≫ Pi.lift (fun t => Pi.π (fun i => T.obj (P i)) (ρ t) ≫ T.map (c t)) := by
  apply Pi.hom_ext
  intro i
  simp only [Category.assoc, piComparison_comp_π, Pi.lift_comp_π]
  rw [← T.map_comp, Pi.lift_comp_π, T.map_comp, piComparison_comp_π_assoc]

include hc in
omit [HasProducts.{v} A] [HasProducts.{v} B] [PreservesLimitsOfSize.{v, v} T] in
theorem mapped_compatibility (a b : ℕ) (θ : Fin (b + 1) → Fin (a + 1)) (t : Fin (a + 1) → κ) :
    T.map (c b (t ∘ θ)) ≫ (J ⋙ T).map (Presentation.ResolutionFaceMaps.productMap G θ t).op =
      (H ⋙ T).map (Presentation.ResolutionFaceMaps.productMap F θ (ρ ∘ t)).op ≫ T.map (c a t) :=
  (T.map_comp _ _).symm.trans ((congrArg T.map (hc a b θ t)).trans (T.map_comp _ _))

theorem coefficientChange_natural :
    Functor.whiskerRight (CosimplicialRefinement.map F G ρ H J c hc) T ≫
      (AlgebraicGeometry.Crystalline.Cohomology.Cech.CoefficientChange.CechCoefficientChange.cosimplicialIso T (NonemptyCechNerve.nerve G) J).hom =
    (AlgebraicGeometry.Crystalline.Cohomology.Cech.CoefficientChange.CechCoefficientChange.cosimplicialIso T (NonemptyCechNerve.nerve F) H).hom ≫
      CosimplicialRefinement.map F G ρ (H ⋙ T) (J ⋙ T) (fun a t => T.map (c a t))
        (mapped_compatibility F G ρ H J c hc T) := by
  apply NatTrans.ext
  funext a
  exact piComparison_reindex (fun t : Fin (a.len + 1) → κ => ρ ∘ t) T
    (P := fun t => H.obj (op (Presentation.TupleProducts.family F a.len t)))
    (Q := fun t => J.obj (op (Presentation.TupleProducts.family G a.len t))) (c a.len)

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Frame.CosimplicialRefinement

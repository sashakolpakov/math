import OAI.NumberTheory.PadicHodge.IntegralComparison.FrameCech.Transformation
import OAI.AlgebraicGeometry.Crystalline.Cohomology.Cech.CoefficientChangeNaturality

/-! # Cosimplicial Transformation -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Frame.CosimplicialTransformation

noncomputable section

/-! Compatible maps of actual tuple coefficients induce a cosimplicial
map. The construction retains the coefficient category, so it applies
before forgetting ring multiplication. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits Opposite Simplicial

universe u v t s

variable {C D : Type (max u v)} [Category.{v} C] [Category.{v} D]
  [HasBinaryProducts C] [HasBinaryProducts D] {ι : Type v} (F : ι → C) (G : ι → D)
  {A : Type t} [Category.{s} A] [HasProducts.{v} A]
  (H : Cᵒᵖ ⥤ A) (J : Dᵒᵖ ⥤ A)
  (c : ∀ (a : ℕ) (t : Fin (a + 1) → ι),
    H.obj (op (Presentation.TupleProducts.family F a t)) ⟶
      J.obj (op (Presentation.TupleProducts.family G a t)))
  (hc : ∀ (a b : ℕ) (θ : Fin (b + 1) → Fin (a + 1)) (t : Fin (a + 1) → ι),
    c b (t ∘ θ) ≫ J.map (Presentation.ResolutionFaceMaps.productMap G θ t).op =
      H.map (Presentation.ResolutionFaceMaps.productMap F θ t).op ≫ c a t)

def map :
    (FormalCoproduct.cosimplicialObjectFunctor (NonemptyCechNerve.nerve F)).obj H ⟶
      (FormalCoproduct.cosimplicialObjectFunctor (NonemptyCechNerve.nerve G)).obj J where
  app a := Limits.Pi.map (c a.len)
  naturality {a b} θ := by
    let Hₐ := fun t => H.obj (op (Presentation.TupleProducts.family F a.len t))
    let Hᵦ := fun t => H.obj (op (Presentation.TupleProducts.family F b.len t))
    let Jₐ := fun t => J.obj (op (Presentation.TupleProducts.family G a.len t))
    let Jᵦ := fun t => J.obj (op (Presentation.TupleProducts.family G b.len t))
    let α := ((FormalCoproduct.cosimplicialObjectFunctor (NonemptyCechNerve.nerve F)).obj H).map θ
    let β := ((FormalCoproduct.cosimplicialObjectFunctor (NonemptyCechNerve.nerve G)).obj J).map θ
    apply Pi.hom_ext
    intro t
    let s := t ∘ θ.toOrderHom.toFun
    let h := H.map (Presentation.ResolutionFaceMaps.productMap F θ.toOrderHom.toFun t).op
    let j := J.map (Presentation.ResolutionFaceMaps.productMap G θ.toOrderHom.toFun t).op
    have hα : α ≫ Pi.π Hᵦ t = Pi.π Hₐ s ≫ h := Pi.lift_comp_π _ t
    have hβ : β ≫ Pi.π Jᵦ t = Pi.π Jₐ s ≫ j := Pi.lift_comp_π _ t
    have hleft : (α ≫ Limits.Pi.map (c b.len)) ≫ Pi.π Jᵦ t =
        Pi.π Hₐ s ≫ (h ≫ c b.len t) :=
      (Category.assoc _ _ _).trans
        ((congrArg (fun q => α ≫ q) (Pi.map_π (c b.len) t)).trans
          ((Category.assoc _ _ _).symm.trans
            ((congrArg (fun q => q ≫ c b.len t) hα).trans (Category.assoc _ _ _))))
    have hright : (Limits.Pi.map (c a.len) ≫ β) ≫ Pi.π Jᵦ t =
        Pi.π Hₐ s ≫ (c a.len s ≫ j) :=
      (Category.assoc _ _ _).trans
        ((congrArg (fun q => Limits.Pi.map (c a.len) ≫ q) hβ).trans
          ((Category.assoc _ _ _).symm.trans
            ((congrArg (fun q => q ≫ j) (Pi.map_π (c a.len) s)).trans (Category.assoc _ _ _))))
    exact hleft.trans ((congrArg (fun q => Pi.π Hₐ s ≫ q)
      (hc b.len a.len θ.toOrderHom.toFun t).symm).trans hright.symm)

variable {B : Type t} [Category.{s} B] [HasProducts.{v} B]
  (T : A ⥤ B) [PreservesLimitsOfSize.{v, v} T]

include hc in
omit [HasProducts.{v} A] [HasProducts.{v} B] [PreservesLimitsOfSize.{v, v} T] in
theorem mapped_compatibility (a b : ℕ) (θ : Fin (b + 1) → Fin (a + 1)) (t : Fin (a + 1) → ι) :
    T.map (c b (t ∘ θ)) ≫ (J ⋙ T).map (Presentation.ResolutionFaceMaps.productMap G θ t).op =
      (H ⋙ T).map (Presentation.ResolutionFaceMaps.productMap F θ t).op ≫ T.map (c a t) :=
  (T.map_comp _ _).symm.trans ((congrArg T.map (hc a b θ t)).trans (T.map_comp _ _))

theorem coefficientChange_natural :
    Functor.whiskerRight (CosimplicialTransformation.map F G H J c hc) T ≫
      (AlgebraicGeometry.Crystalline.Cohomology.Cech.CoefficientChange.CechCoefficientChange.cosimplicialIso T (NonemptyCechNerve.nerve G) J).hom =
    (AlgebraicGeometry.Crystalline.Cohomology.Cech.CoefficientChange.CechCoefficientChange.cosimplicialIso T (NonemptyCechNerve.nerve F) H).hom ≫
      CosimplicialTransformation.map F G (H ⋙ T) (J ⋙ T) (fun a t => T.map (c a t))
        (mapped_compatibility F G H J c hc T) := by
  apply NatTrans.ext
  funext a
  exact AlgebraicGeometry.Crystalline.Cohomology.Cech.CoefficientChangeNaturality.CechCoefficientChangeNaturality.piComparison_map T (c a.len)

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Frame.CosimplicialTransformation

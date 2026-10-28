import OAI.AlgebraicGeometry.Comparison.Betti.FunctorialCokernel

/-! # Relative Quotient Map -/

namespace OAI.AlgebraicGeometry.Comparison.Betti.RelativeQuotientMap.Resolution

noncomputable section

/-! A natural comparison preserving the original units descends to the actual cokernels, without exactness of the intervening functor. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits

variable {C D : Type*} [Category* C] [Category* D] [Abelian C] [Abelian D]
  (T : C ⥤ C) (η : 𝟭 C ⟶ T) (S : D ⥤ D) (θ : 𝟭 D ⟶ S)
  (F : D ⥤ C) [F.Additive] (α : F ⋙ T ⟶ S ⋙ F)
  (hα : ∀ B, η.app (F.obj B) ≫ α.app B = F.map (θ.app B))

include hα

theorem relativeQuotientMap_zero {A : C} {B : D} (u : A ⟶ F.obj B) :
    η.app A ≫ (T.map u ≫ α.app B ≫ F.map (cokernel.π (θ.app B))) = 0 := by
  rw [← Category.assoc, ← Category.assoc, ← η.naturality u, Category.assoc,
    Category.assoc, ← Category.assoc (η.app (F.obj B)), hα B,
    ← F.map_comp, cokernel.condition, F.map_zero, comp_zero]

def relativeQuotientMap {A : C} {B : D} (u : A ⟶ F.obj B) :
    (FunctorialCokernel.Resolution.quotientFunctor T η).obj A ⟶ F.obj ((FunctorialCokernel.Resolution.quotientFunctor S θ).obj B) :=
  cokernel.desc (η.app A) (T.map u ≫ α.app B ≫ F.map (cokernel.π (θ.app B)))
    (relativeQuotientMap_zero T η S θ F α hα u)

theorem relativeQuotientMap_π {A : C} {B : D} (u : A ⟶ F.obj B) :
    cokernel.π (η.app A) ≫ relativeQuotientMap T η S θ F α hα u =
      T.map u ≫ α.app B ≫ F.map (cokernel.π (θ.app B)) :=
  cokernel.π_desc _ _ _

theorem relativeQuotientMap_naturality {A A' : C} {B B' : D}
    (u : A ⟶ F.obj B) (u' : A' ⟶ F.obj B') (a : A ⟶ A') (b : B ⟶ B')
    (hu : a ≫ u' = u ≫ F.map b) :
    (FunctorialCokernel.Resolution.quotientFunctor T η).map a ≫ relativeQuotientMap T η S θ F α hα u' =
      relativeQuotientMap T η S θ F α hα u ≫ F.map ((FunctorialCokernel.Resolution.quotientFunctor S θ).map b) := by
  apply (cancel_epi (cokernel.π (η.app A))).mp
  change cokernel.π (η.app A) ≫ ((FunctorialCokernel.Resolution.quotientFunctor T η).map a ≫ _) =
    cokernel.π (η.app A) ≫ (_ ≫ F.map ((FunctorialCokernel.Resolution.quotientFunctor S θ).map b))
  erw [← Category.assoc, ← (FunctorialCokernel.Resolution.quotientProjection T η).naturality a, Category.assoc,
    relativeQuotientMap_π,
    ← Category.assoc (cokernel.π (η.app A)) (relativeQuotientMap T η S θ F α hα u),
    relativeQuotientMap_π]
  erw [← Category.assoc (T.map a), ← T.map_comp, hu, T.map_comp, Category.assoc,
    ← Category.assoc (T.map (F.map b)), α.naturality b, Category.assoc]
  have hb : F.map (S.map b) ≫ F.map (cokernel.π (θ.app B')) =
      F.map (cokernel.π (θ.app B)) ≫ F.map ((FunctorialCokernel.Resolution.quotientFunctor S θ).map b) :=
    (F.map_comp _ _).symm.trans
      ((congrArg F.map ((FunctorialCokernel.Resolution.quotientProjection S θ).naturality b)).trans (F.map_comp _ _))
  calc
    _ = T.map u ≫ α.app B ≫
        (F.map (cokernel.π (θ.app B)) ≫ F.map ((FunctorialCokernel.Resolution.quotientFunctor S θ).map b)) :=
      congrArg (fun v => T.map u ≫ α.app B ≫ v) hb
    _ = _ := (congrArg (T.map u ≫ ·) (Category.assoc _ _ _).symm).trans
      (Category.assoc _ _ _).symm

end

end OAI.AlgebraicGeometry.Comparison.Betti.RelativeQuotientMap.Resolution

import OAI.AlgebraicGeometry.SheafCohomology.Projective.AdditiveCoproductMatrix

/-! # Additive Coproduct Coordinates -/

namespace OAI.AlgebraicGeometry.SheafCohomology.Projective.AdditiveCoproductCoordinates

noncomputable section

/-! Finite coproduct matrices after independent linear coordinates on each summand. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.CategoryTheory.Preadditive
universe u v w t
variable {C : Type u} [Category.{v} C] [Preadditive C] [HasFiniteBiproducts C]
variable {R : Type w} [CommRing R] (F : C ⥤ ModuleCat.{t} R) [F.Additive]
variable {ι κ : Type} [Fintype ι] [Fintype κ]

def additiveCoproductCoordinates (M : ι → C) (V : ι → ModuleCat.{t} R)
    (e : ∀ i, F.obj (M i) ≃ₗ[R] V i) : F.obj (∐ M) ≃ₗ[R] (∀ i, V i) :=
  (AdditiveCoproductSections.additiveCoproductIsoPi F M).toLinearEquiv.trans (LinearEquiv.piCongrRight e)

theorem additiveCoproductCoordinates_apply (M : ι → C) (V : ι → ModuleCat.{t} R)
    (e : ∀ i, F.obj (M i) ≃ₗ[R] V i) (x : F.obj (∐ M)) (i : ι) :
    additiveCoproductCoordinates F M V e x i = e i (F.map (CoproductMatrixComponents.finiteCoproductProjection M i) x) := by
  simp only [additiveCoproductCoordinates, LinearEquiv.trans_apply,
    LinearEquiv.piCongrRight_apply]
  change e i ((AdditiveCoproductSections.additiveCoproductIsoPi F M).hom x i) = _
  rw [AdditiveCoproductMatrix.additiveCoproductIsoPi_hom_apply]

theorem additiveCoproductCoordinates_reassemble
    (M : ι → C) (V : ι → ModuleCat.{t} R)
    (e : ∀ i, F.obj (M i) ≃ₗ[R] V i)
    {H : Type t} [AddCommGroup H] [Module R H] (p : H ≃ₗ[R] (∀ i, V i))
    (x : F.obj (∐ M)) (i : ι) :
    p (((additiveCoproductCoordinates F M V e).trans p.symm).toModuleIso.hom x) i =
      e i (F.map (CoproductMatrixComponents.finiteCoproductProjection M i) x) := by
  change p (p.symm (additiveCoproductCoordinates F M V e x)) i = _
  rw [p.apply_symm_apply, additiveCoproductCoordinates_apply]

theorem additiveCoproductCoordinates_map (M : ι → C) (N : κ → C)
    (V : ι → ModuleCat.{t} R) (W : κ → ModuleCat.{t} R)
    (e : ∀ i, F.obj (M i) ≃ₗ[R] V i) (d : ∀ j, F.obj (N j) ≃ₗ[R] W j)
    (f : (∐ M) ⟶ ∐ N) (x : F.obj (∐ M)) (j : κ) :
    additiveCoproductCoordinates F N W d (F.map f x) j =
      ∑ i, d j (F.map (Sigma.ι M i ≫ f ≫ CoproductMatrixComponents.finiteCoproductProjection N j)
        ((e i).symm (additiveCoproductCoordinates F M V e x i))) := by
  simp only [additiveCoproductCoordinates, LinearEquiv.trans_apply,
    LinearEquiv.piCongrRight_apply, LinearEquiv.symm_apply_apply]
  change d j ((AdditiveCoproductSections.additiveCoproductIsoPi F N).hom (F.map f x) j) =
    ∑ i, d j (F.map (Sigma.ι M i ≫ f ≫ CoproductMatrixComponents.finiteCoproductProjection N j)
      ((AdditiveCoproductSections.additiveCoproductIsoPi F M).hom x i))
  rw [AdditiveCoproductMatrix.additiveCoproductMatrix_apply, map_sum]

end

end OAI.AlgebraicGeometry.SheafCohomology.Projective.AdditiveCoproductCoordinates

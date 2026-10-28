import OAI.NumberTheory.PadicHodge.IntegralComparison.ProjectiveResolution.HomNaturality

/-! # Homotopy Naturality -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.ProjectiveResolution.HomotopyNaturality

noncomputable section

/-! Canonical resolution comparison commutes with every actual
augmentation-preserving lift by a genuine cochain homotopy. -/
open _root_.CategoryTheory Opposite
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
universe u v w z
variable {C : Type u} [Category.{v} C] [Abelian C]
  {D : Type w} [Category.{z} D] [Abelian D]
  (F : Cᵒᵖ ⥤ D) [F.Additive]

def naturality {M N : C} (f : M ⟶ N)
    (P P' : ProjectiveResolution M) (Q Q' : ProjectiveResolution N)
    (a : P.complex ⟶ Q.complex) (b : P'.complex ⟶ Q'.complex)
    (ha : a ≫ Q.π = P.π ≫ (ChainComplex.single₀ C).map f)
    (hb : b ≫ Q'.π = P'.π ≫ (ChainComplex.single₀ C).map f) :
    Homotopy
      ((HomNaturality.functor F).map a.op ≫
        (Hom.Comparison.homotopyEquiv F P P').hom)
      ((Hom.Comparison.homotopyEquiv F Q Q').hom ≫
        (HomNaturality.functor F).map b.op) := by
  have hiP : ProjectiveResolution.lift (𝟙 M) P' P ≫ P.π = P'.π := by
    simp
  have hiQ : ProjectiveResolution.lift (𝟙 N) Q' Q ≫ Q.π = Q'.π := by
    simp
  let h : Homotopy (ProjectiveResolution.lift (𝟙 M) P' P ≫ a)
      (b ≫ ProjectiveResolution.lift (𝟙 N) Q' Q) :=
    ProjectiveResolution.liftHomotopy f _ _ (by
      rw [Category.assoc, ha, ← Category.assoc, hiP]) (by
      rw [Category.assoc, hiQ, hb])
  have he := F.mapHomotopy h.op
  change Homotopy
    ((HomNaturality.functor F).map
      (ProjectiveResolution.lift (𝟙 M) P' P ≫ a).op)
    ((HomNaturality.functor F).map
      (b ≫ ProjectiveResolution.lift (𝟙 N) Q' Q).op) at he
  simp only [op_comp, CategoryTheory.Functor.map_comp] at he
  exact he

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.ProjectiveResolution.HomotopyNaturality

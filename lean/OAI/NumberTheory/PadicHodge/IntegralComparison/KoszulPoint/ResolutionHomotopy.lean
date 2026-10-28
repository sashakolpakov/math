import OAI.NumberTheory.PadicHodge.IntegralComparison.KoszulPoint.Resolution
import OAI.NumberTheory.PadicHodge.IntegralComparison.ProjectiveResolution.HomotopyNaturality

/-! # Resolution Homotopy -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.KoszulPoint.ResolutionHomotopy

noncomputable section

/-! The product-to-concatenated point comparison is compatible with the
original resolution by an actual cochain homotopy for every additive
coefficient functor. -/
open _root_.CategoryTheory Opposite _root_.HomologicalComplex
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w z

private def augmentationHomotopy
    {C : Type u} [Category.{v} C] [Abelian C]
    {D : Type w} [Category.{z} D] [Abelian D]
    (F : Cᵒᵖ ⥤ D) [F.Additive] {M : C}
    (Q T S : ProjectiveResolution M) (a : S.complex ⟶ T.complex)
    (ha : a ≫ T.π = S.π) :
    Homotopy
      ((IntegralComparison.ProjectiveResolution.Hom.Comparison.homotopyEquiv F Q T).hom ≫
        (IntegralComparison.ProjectiveResolution.HomNaturality.functor F).map a.op)
      (IntegralComparison.ProjectiveResolution.Hom.Comparison.homotopyEquiv F Q S).hom := by
  let h : Homotopy (a ≫ ProjectiveResolution.lift (𝟙 M) T Q)
      (ProjectiveResolution.lift (𝟙 M) S Q) :=
    ProjectiveResolution.liftHomotopy (𝟙 M) _ _
      (by simp [Category.assoc, ha]) (by simp)
  have he := F.mapHomotopy h.op
  change Homotopy
    ((IntegralComparison.ProjectiveResolution.HomNaturality.functor F).map
      (a ≫ ProjectiveResolution.lift (𝟙 M) T Q).op)
    ((IntegralComparison.ProjectiveResolution.HomNaturality.functor F).map
      (ProjectiveResolution.lift (𝟙 M) S Q).op) at he
  simp only [op_comp, CategoryTheory.Functor.map_comp] at he
  exact he

variable (R : Type u) [CommRing R] {c m : ℕ}
  (s : Fin c → R) (t : Fin m → R)
  (hst : RingTheory.Sequence.IsWeaklyRegular R (List.ofFn (Fin.append s t)))
  {D : Type w} [Category.{z} D] [Abelian D]
  (F : (ModuleCat.{u} R)ᵒᵖ ⥤ D) [F.Additive]
  (Q : ProjectiveResolution (ModuleCat.of R (R ⧸ KoszulPartial.Resolution.pointIdeal R s t)))

abbrev homotopy := augmentationHomotopy F Q
  (KoszulPartial.Resolution.pointResolution R s t hst)
  (Resolution.Comparison.fullResolution R s t hst)
  (Koszul.DuplicateFraction.pointIso R s t).hom
  (Resolution.Comparison.augmentation R s t hst)

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.KoszulPoint.ResolutionHomotopy

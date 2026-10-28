import OAI.AlgebraicGeometry.FormalGeometry.Completion.Geometric.MapFaithful
import OAI.AlgebraicGeometry.FormalGeometry.Completion.TorsionPointDetection

/-! # Etale Hom -/

namespace OAI.AlgebraicGeometry.FormalGeometry.Completion.Finite.EtaleHom.Construction

noncomputable section

/-! There are finitely many actual morphisms from a finite etale scheme to a finite field scheme. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
open MonoidalCategory

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

universe u

/-- Actual points detect maps from finite etale schemes over an algebraically closed field. -/
theorem finite_etale_hom_of_isAlgClosed {K : Type u} [Field K] [IsAlgClosed K]
    (X Y : Over (Spec (CommRingCat.of K))) [IsFinite X.hom] [Etale X.hom]
    [IsFinite Y.hom] : Finite (X ⟶ Y) := by
  have : IsReduced X.left := Quotients.FiniteDescent.SchemeSmooth.Construction.SchemeSmoothReduced.reduced_of_smooth_field X.hom
  have := TorsionPointAction.Construction.finite_field_points X
  have := TorsionPointAction.Construction.finite_field_points Y
  let ev : (X ⟶ Y) → ((𝟙_ (Over (Spec (CommRingCat.of K))) ⟶ X) →
      (𝟙_ (Over (Spec (CommRingCat.of K))) ⟶ Y)) := fun f a => a ≫ f
  apply Finite.of_injective ev
  intro f g h
  exact TorsionPointDetection.Construction.over_hom_ext_of_field_points f g (fun a => congrFun h a)

/-- Finiteness of the actual morphism set descends from geometric base change. -/
theorem finite_etale_hom {K : Type u} [Field K]
    (X Y : Over (Spec (CommRingCat.of K))) [IsFinite X.hom] [Etale X.hom]
    [IsFinite Y.hom] : Finite (X ⟶ Y) := by
  have : IsFinite (Geometric.Frobenius.Construction.geometricFiberOver K X).hom :=
    inferInstanceAs (IsFinite (pullback.snd X.hom (Geometric.Frobenius.Construction.algebraicClosureBase K)))
  have : Etale (Geometric.Frobenius.Construction.geometricFiberOver K X).hom :=
    inferInstanceAs (Etale (pullback.snd X.hom (Geometric.Frobenius.Construction.algebraicClosureBase K)))
  have : IsFinite (Geometric.Frobenius.Construction.geometricFiberOver K Y).hom :=
    inferInstanceAs (IsFinite (pullback.snd Y.hom (Geometric.Frobenius.Construction.algebraicClosureBase K)))
  have := finite_etale_hom_of_isAlgClosed (Geometric.Frobenius.Construction.geometricFiberOver K X) (Geometric.Frobenius.Construction.geometricFiberOver K Y)
  apply Finite.of_injective ((Over.pullback (Geometric.Frobenius.Construction.algebraicClosureBase K)).map (X := X) (Y := Y))
  intro f g h
  apply Geometric.MapFaithful.Construction.geometricFiberMap_injective K
  exact congrArg (fun a : Geometric.Frobenius.Construction.geometricFiberOver K X ⟶ Geometric.Frobenius.Construction.geometricFiberOver K Y => a.left) h

end

end OAI.AlgebraicGeometry.FormalGeometry.Completion.Finite.EtaleHom.Construction

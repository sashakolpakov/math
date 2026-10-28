import OAI.AlgebraicGeometry.FormalGeometry.Completion.FiniteTorsor.App

/-! # Torsor Sheaf -/

namespace OAI.AlgebraicGeometry.FormalGeometry.Completion.FiniteTorsor

noncomputable section

/-!
# Completion: the sheaf of local lifts of a finite-coefficient extension

The local torsor is a sheaf: whether a section projects to the integer
generator is a local equality in the integer constant sheaf.
-/

open _root_.CategoryTheory Limits _root_.AlgebraicGeometry Opposite Abelian

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

universe u

variable {ℓ n : ℕ} {X : Scheme.{u}} (E : App.Construction.FiniteCoefficientExtension ℓ n X)

/-- The fiber, as a subpresheaf of the middle term's underlying presheaf. -/
def App.Construction.FiniteCoefficientExtension.fiberSubfunctor : Subfunctor (E.middle.obj ⋙ forget Ab.{u + 1}) where
  obj U := {s | E.projection.hom.app U s = App.Construction.proEtIntegerLocalGenerator X U.unop}
  map := by
    intro U V f s hs
    change E.projection.hom.app V (E.middle.obj.map f s) = _
    rw [NatTrans.naturality_apply, hs]
    exact App.Construction.proEtIntegerLocalGenerator_naturality X f.unop

/-- The fiber presheaf satisfies the sheaf condition on the actual site. -/
theorem App.Construction.FiniteCoefficientExtension.fiberPresheaf_isSheaf :
    Presheaf.IsSheaf (Scheme.ProEt.topology X) E.fiberPresheaf := by
  change Presheaf.IsSheaf _ E.fiberSubfunctor.toFunctor
  rw [isSheaf_iff_isSheaf_of_type]
  have hE : Presieve.IsSheaf (Scheme.ProEt.topology X) (E.middle.obj ⋙ forget Ab.{u + 1}) :=
    (isSheaf_iff_isSheaf_of_type _ _).mp
      ((sheafCompose _ (forget Ab.{u + 1})).obj E.middle).property
  have hZ : Presieve.IsSheaf (Scheme.ProEt.topology X)
      ((ProetalePullback.Construction.proEtIntegerConstant X).obj ⋙ forget Ab.{u + 1}) :=
    (isSheaf_iff_isSheaf_of_type _ _).mp
      ((sheafCompose _ (forget Ab.{u + 1})).obj (ProetalePullback.Construction.proEtIntegerConstant X)).property
  apply (Subfunctor.isSheaf_iff E.fiberSubfunctor hE).mpr
  intro U s hs
  apply (hZ _ hs).isSeparatedFor.ext
  intro V f hf
  change (ProetalePullback.Construction.proEtIntegerConstant X).obj.map f.op (E.projection.hom.app U s) =
    (ProetalePullback.Construction.proEtIntegerConstant X).obj.map f.op (App.Construction.proEtIntegerLocalGenerator X U.unop)
  rw [← NatTrans.naturality_apply, App.Construction.proEtIntegerLocalGenerator_naturality]
  exact hf

/-- The actual sheaf of torsor sections attached to the extension. -/
def App.Construction.FiniteCoefficientExtension.fiberSheaf : Sheaf (Scheme.ProEt.topology X) (Type (u + 1)) :=
  ⟨E.fiberPresheaf, E.fiberPresheaf_isSheaf⟩

end

end OAI.AlgebraicGeometry.FormalGeometry.Completion.FiniteTorsor

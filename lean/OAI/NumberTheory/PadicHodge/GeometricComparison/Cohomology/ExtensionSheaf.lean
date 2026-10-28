import OAI.NumberTheory.PadicHodge.GeometricComparison.Cohomology.ExtensionOf

/-! # Extension Sheaf -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.Cohomology

noncomputable section

/-!
# GeometricComparison: the sheaf of local lifts of a coefficient extension

The local torsor is a sheaf: whether a section projects to the integer
generator is a local equality in the integer constant sheaf.
-/

open _root_.CategoryTheory Limits _root_.AlgebraicGeometry Opposite Abelian

universe u

variable {X : Scheme.{u}} {F : Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}} (E : ExtensionOf.CohomologyExtension.Extension X F)

/-- The fiber, as a subpresheaf of the middle term's underlying presheaf. -/
def ExtensionOf.CohomologyExtension.Extension.fiberSubfunctor : Subfunctor (E.middle.obj ⋙ forget Ab.{u + 1}) where
  obj U := {s | E.projection.hom.app U s = AlgebraicGeometry.FormalGeometry.Completion.FiniteTorsor.App.Construction.proEtIntegerLocalGenerator X U.unop}
  map := by
    intro U V f s hs
    change E.projection.hom.app V (E.middle.obj.map f s) = _
    rw [NatTrans.naturality_apply, hs]
    exact AlgebraicGeometry.FormalGeometry.Completion.FiniteTorsor.App.Construction.proEtIntegerLocalGenerator_naturality X f.unop

/-- The fiber presheaf satisfies the sheaf condition on the actual site. -/
theorem ExtensionOf.CohomologyExtension.Extension.fiberPresheaf_isSheaf :
    Presheaf.IsSheaf (Scheme.ProEt.topology X) E.fiberPresheaf := by
  change Presheaf.IsSheaf _ E.fiberSubfunctor.toFunctor
  rw [isSheaf_iff_isSheaf_of_type]
  have hE : Presieve.IsSheaf (Scheme.ProEt.topology X) (E.middle.obj ⋙ forget Ab.{u + 1}) :=
    (isSheaf_iff_isSheaf_of_type _ _).mp
      ((sheafCompose _ (forget Ab.{u + 1})).obj E.middle).property
  have hZ : Presieve.IsSheaf (Scheme.ProEt.topology X)
      ((AlgebraicGeometry.FormalGeometry.Completion.ProetalePullback.Construction.proEtIntegerConstant X).obj ⋙ forget Ab.{u + 1}) :=
    (isSheaf_iff_isSheaf_of_type _ _).mp
      ((sheafCompose _ (forget Ab.{u + 1})).obj (AlgebraicGeometry.FormalGeometry.Completion.ProetalePullback.Construction.proEtIntegerConstant X)).property
  apply (Subfunctor.isSheaf_iff E.fiberSubfunctor hE).mpr
  intro U s hs
  apply (hZ _ hs).isSeparatedFor.ext
  intro V f hf
  change (AlgebraicGeometry.FormalGeometry.Completion.ProetalePullback.Construction.proEtIntegerConstant X).obj.map f.op (E.projection.hom.app U s) =
    (AlgebraicGeometry.FormalGeometry.Completion.ProetalePullback.Construction.proEtIntegerConstant X).obj.map f.op (AlgebraicGeometry.FormalGeometry.Completion.FiniteTorsor.App.Construction.proEtIntegerLocalGenerator X U.unop)
  rw [← NatTrans.naturality_apply, AlgebraicGeometry.FormalGeometry.Completion.FiniteTorsor.App.Construction.proEtIntegerLocalGenerator_naturality]
  exact hf

/-- The actual sheaf of torsor sections attached to the extension. -/
def ExtensionOf.CohomologyExtension.Extension.fiberSheaf : Sheaf (Scheme.ProEt.topology X) (Type (u + 1)) :=
  ⟨E.fiberPresheaf, E.fiberPresheaf_isSheaf⟩

end

end OAI.NumberTheory.PadicHodge.GeometricComparison.Cohomology

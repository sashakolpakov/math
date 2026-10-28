import OAI.AlgebraicGeometry.FormalGeometry.Completion.ProetalePullback
import OAI.NumberTheory.PadicHodge.IntegralComparison.ProEtale

/-! # Pro Etale Structure -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.ProEtaleStructure.ProEtaleIsoSite

noncomputable section

/-! Actual base change by a scheme isomorphism agrees with transport of pro-étale objects. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

open OAI.AlgebraicGeometry.FormalGeometry.Completion.ProetalePullback.Construction OAI.NumberTheory.PadicHodge.IntegralComparison.ProEtale

universe u
variable {X Y : Scheme.{u}} (e : X ≅ Y)

private theorem projection_structure {U : Scheme.{u}} (f : U ⟶ Y) :
    pullback.fst f e.hom ≫ (f ≫ e.inv) = pullback.snd f e.hom := by
  rw [← Category.assoc, pullback.condition, Category.assoc, e.hom_inv_id, Category.comp_id]

def projectionIso {U : Scheme.{u}} (f : U ⟶ Y) : pullback f e.hom ≅ U :=
  asIso (pullback.fst f e.hom)

def component (U : Y.ProEt) :
    (AlgebraicGeometry.FormalGeometry.Completion.ProetalePullback.Construction.proEtBaseChange e.hom).obj U ≅ (IntegralComparison.ProEtale.proEtaleCongr e.symm).functor.obj U :=
  MorphismProperty.Over.isoMk (projectionIso e U.hom) (projection_structure e U.hom)

def baseChangeIso : AlgebraicGeometry.FormalGeometry.Completion.ProetalePullback.Construction.proEtBaseChange e.hom ≅ (IntegralComparison.ProEtale.proEtaleCongr e.symm).functor :=
  NatIso.ofComponents (component e) (fun {U V} f => by
    apply MorphismProperty.Over.Hom.ext
    change ((AlgebraicGeometry.FormalGeometry.Completion.ProetalePullback.Construction.proEtBaseChange e.hom).map f).left ≫ pullback.fst V.hom e.hom =
      pullback.fst U.hom e.hom ≫ f.left
    exact pullback.lift_fst _ _ _)

end

end OAI.NumberTheory.PadicHodge.GeometricComparison.ProEtaleStructure.ProEtaleIsoSite

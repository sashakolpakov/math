import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Module.PresheafComponentEnd
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.LineBundle.EndRing
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Global.ScalarBaseChange

/-! # Presheaf Extended Scalars -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Section.PresheafExtendedScalars

noncomputable section

/-! Functions from the changed base act on pushed-forward module sections, with the original coefficient action recovered on base scalars. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

variable {X Y : Scheme.{u}} {R B : Type u} [CommRing R] [CommRing B] [Algebra R B]
variable (a : Y ⟶ X) (f : R →+* Γ(X, ⊤)) (M : Y.Modules) (q : B →+* Γ(Y, ⊤))

def pushedCoefficientScalarRingHom : B →+* End (Coefficient.ModulePresheaf.coefficientModulePresheaf f ((Scheme.Modules.pushforward a).obj M)) :=
  (Coefficient.PresheafScalarAction.coefficientPresheafEndRingHom f ((Scheme.Modules.pushforward a).obj M)).comp
    ((LineBundle.EndRing.moduleFunctorEndRingHom (Scheme.Modules.pushforward a) M).comp
      ((Global.ScalarRingAction.globalModuleScalarRingHom M).comp q))

theorem pushedCoefficientScalarRingHom_coefficient
    (hq : q.comp (algebraMap R B) = a.appTop.hom.comp f) (r : R) :
    pushedCoefficientScalarRingHom a f M q (algebraMap R B r) =
      Coefficient.PresheafScalarAction.coefficientPresheafGlobalScalarRingHom f ((Scheme.Modules.pushforward a).obj M) (f r) := by
  change (Coefficient.ModulePresheafFunctor.coefficientModulePresheafFunctor f).map
    ((Scheme.Modules.pushforward a).map (Global.ModuleScalars.globalModuleScalar M (q (algebraMap R B r)))) =
      (Coefficient.ModulePresheafFunctor.coefficientModulePresheafFunctor f).map (Global.ModuleScalars.globalModuleScalar ((Scheme.Modules.pushforward a).obj M) (f r))
  apply congrArg (Coefficient.ModulePresheafFunctor.coefficientModulePresheafFunctor f).map
  have h : q (algebraMap R B r) = a.appTop (f r) := DFunLike.congr_fun hq r
  exact (congrArg (fun c => (Scheme.Modules.pushforward a).map (Global.ModuleScalars.globalModuleScalar M c)) h).trans
    (Global.ScalarBaseChange.globalModuleScalar_pushforward a M (f r))

def pushedCoefficientScalarComponent (U : X.Opens) :
    B →+* Module.End R ((Coefficient.ModulePresheaf.coefficientModulePresheaf f ((Scheme.Modules.pushforward a).obj M)).obj (.op U)) :=
  (HilbertConstruction.Module.PresheafComponentEnd.modulePresheafComponentEndRingHom _ U).comp (pushedCoefficientScalarRingHom a f M q)

theorem pushedCoefficientScalarComponent_coefficient
    (hq : q.comp (algebraMap R B) = a.appTop.hom.comp f) (U : X.Opens) (r : R)
    (x : (Coefficient.ModulePresheaf.coefficientModulePresheaf f ((Scheme.Modules.pushforward a).obj M)).obj (.op U)) :
    pushedCoefficientScalarComponent a f M q U (algebraMap R B r) x = r • x :=
  (congrArg (fun e : End (Coefficient.ModulePresheaf.coefficientModulePresheaf f ((Scheme.Modules.pushforward a).obj M)) =>
    e.app (.op U) x) (pushedCoefficientScalarRingHom_coefficient a f M q hq r)).trans
      (Coefficient.PresheafScalarAction.coefficientPresheafGlobalScalarRingHom_coefficient f ((Scheme.Modules.pushforward a).obj M) r U x)

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Section.PresheafExtendedScalars

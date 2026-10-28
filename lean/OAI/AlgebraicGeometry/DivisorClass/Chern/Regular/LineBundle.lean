import OAI.AlgebraicGeometry.DivisorClass.Chern.Regular.LineModuleSheaf
import OAI.AlgebraicGeometry.DivisorClass.Chern.Regular.LineSectionFrames

/-! # Line Bundle -/

namespace OAI.AlgebraicGeometry.DivisorClass.Chern.Regular.LineBundle

noncomputable section

/-! A regular unit cocycle constructs an actual algebraic line bundle with genuine native local trivializations. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace Opposite
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

variable {X : Scheme} {ι : Type} (D : FunctionGluing.RegularLineCocycle X ι)

def regularLineModuleOverIso (i : ι) :
    (LineModuleSheaf.regularLineModuleSheaf D).over (D.domain i) ≅
      SheafOfModules.unit (X.ringCatSheaf.over (D.domain i)) :=
  (SheafOfModules.fullyFaithfulForget _).preimageIso
    (PresheafOfModules.isoMk
      (fun U => (LineSectionFrames.regularLineSectionLinearFrame D i (leOfHom U.unop.hom)).toModuleIso)
      (by
        intro U V f
        apply ModuleCat.hom_ext
        apply LinearMap.ext
        intro s
        exact LineSectionFrames.regularLineSectionFrameValue_restrict D i (leOfHom U.unop.hom)
          (leOfHom f.unop.left) s))

def regularLineModuleNativeIso (i : ι) :
    (LineModuleSheaf.regularLineModuleSheaf D).restrict (D.domain i).ι ≅
      Line.Bundles.Construction.structureModule (D.domain i).toScheme :=
  ((Scheme.Modules.overFunctorEquiv (D.domain i)).app (LineModuleSheaf.regularLineModuleSheaf D)).symm ≪≫
    (Scheme.Modules.overEquiv (D.domain i)).functor.mapIso (regularLineModuleOverIso D i) ≪≫
    ((Scheme.Modules.overFunctorEquiv (D.domain i)).app (Line.Bundles.Construction.structureModule X)) ≪≫
    Scheme.Modules.restrictUnitIso (D.domain i).ι

/-- The constructed module sheaf is locally isomorphic to the original structure sheaf. -/
theorem regularLineModuleSheaf_locallyTrivial (x : X) :
    ∃ U : X.Opens, x ∈ U ∧ Nonempty
      ((LineModuleSheaf.regularLineModuleSheaf D).restrict U.ι ≅ Line.Bundles.Construction.structureModule U.toScheme) := by
  have hx : x ∈ iSup D.domain := by rw [D.covers]; trivial
  obtain ⟨i, hi⟩ := Opens.mem_iSup.mp hx
  exact ⟨D.domain i, hi, ⟨regularLineModuleNativeIso D i⟩⟩

def regularCocycleAlgebraicLineBundle (P : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation)
    (D : FunctionGluing.RegularLineCocycle P.carrier ι) : Line.Bundles.AlgebraicLineBundle P where
  sheaf := LineModuleSheaf.regularLineModuleSheaf D
  locallyTrivial := regularLineModuleSheaf_locallyTrivial D

end

end OAI.AlgebraicGeometry.DivisorClass.Chern.Regular.LineBundle

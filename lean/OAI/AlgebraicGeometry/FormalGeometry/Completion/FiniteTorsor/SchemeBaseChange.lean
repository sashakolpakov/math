import OAI.AlgebraicGeometry.FormalGeometry.Completion.FiniteTorsor.InverseImage
import OAI.AlgebraicGeometry.FormalGeometry.Completion.ProEtale.PullbackRepresentable

/-! # Scheme Base Change -/

namespace OAI.AlgebraicGeometry.FormalGeometry.Completion.FiniteTorsor

noncomputable section

/-!
# Completion: base change of the actual finite étale torsor scheme

The actual torsor scheme of the cohomological pullback is isomorphic over
the new base to the geometric base change of the original representative.
-/

open _root_.CategoryTheory _root_.CategoryTheory.Functor Limits _root_.AlgebraicGeometry

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

universe u

variable {ℓ n : ℕ} [NeZero (ℓ ^ n)] {X Y : Scheme.{u}}

/-- The proved global representative, now as an isomorphism in the sheaf category. -/
def App.Construction.FiniteCoefficientExtension.gluedRepresentativeSheafIso (E : App.Construction.FiniteCoefficientExtension ℓ n X) :
    (Scheme.ProEt.topology X).uliftYoneda.{u + 1}.obj E.gluedProEt ≅ E.fiberSheaf :=
  (asIso E.sectionToGluedSheafHom).symm

variable (E : App.Construction.FiniteCoefficientExtension ℓ n Y) (f : X ⟶ Y)

/-- The original scheme after base change represents the pulled-back extension's torsor. -/
def App.Construction.FiniteCoefficientExtension.baseChangeRepresentativeSheafIso :
    (Scheme.ProEt.topology X).uliftYoneda.{u + 1}.obj
      ((ProetalePullback.Construction.proEtBaseChange f).obj E.gluedProEt) ≅ (E.pullbackExtension f).fiberSheaf :=
  (ProEtale.PullbackRepresentable.Construction.proEtPullbackRepresentableIso f E.gluedProEt).symm ≪≫
    (ProEtale.PullbackTypes.Construction.proEtTypeSheafPullback f).mapIso E.gluedRepresentativeSheafIso ≪≫
      E.inverseImageFiberIso f

/-- The torsor scheme constructed after actual cohomological pullback is its geometric base change. -/
def App.Construction.FiniteCoefficientExtension.baseChangeGluedIso :
    (ProetalePullback.Construction.proEtBaseChange f).obj E.gluedProEt ≅ (E.pullbackExtension f).gluedProEt :=
  (Scheme.ProEt.topology X).uliftYoneda.{u + 1}.preimageIso
    (E.baseChangeRepresentativeSheafIso f ≪≫
      (E.pullbackExtension f).gluedRepresentativeSheafIso.symm)

/-- Vanishing of the actual pulled-back class is detected by a section of the original
torsor's geometric base change. -/
theorem App.Construction.FiniteCoefficientExtension.pullback_eq_zero_iff_baseChange_section :
    Finite.CoefficientPullback.Construction.finiteEllAdicPullback ℓ n f 1 E.extClass = 0 ↔
      Nonempty (Scheme.ProEt.mk (𝟙 X) ⟶ (ProetalePullback.Construction.proEtBaseChange f).obj E.gluedProEt) := by
  rw [← E.pullbackExtension_extClass, (E.pullbackExtension f).class_eq_zero_iff_fiber_nonempty]
  let e := (GlobalSections.Construction.proEtaleIdentityIsTerminal X).uniqueUpToIso terminalIsTerminal
  constructor
  · rintro ⟨s⟩
    exact ⟨e.hom ≫ (E.pullbackExtension f).gluedRepresentative.homEquiv.symm s ≫
      (E.baseChangeGluedIso f).inv⟩
  · rintro ⟨s⟩
    exact ⟨(E.pullbackExtension f).gluedRepresentative.homEquiv
      (e.inv ≫ s ≫ (E.baseChangeGluedIso f).hom)⟩

/-- The actual pullback class vanishes exactly when the base morphism lifts to the
original finite étale torsor scheme. -/
theorem App.Construction.FiniteCoefficientExtension.pullback_eq_zero_iff_lift :
    Finite.CoefficientPullback.Construction.finiteEllAdicPullback ℓ n f 1 E.extClass = 0 ↔
      ∃ s : X ⟶ E.gluedScheme, s ≫ E.gluedSchemeToBase = f := by
  rw [E.pullback_eq_zero_iff_baseChange_section f]
  constructor
  · rintro ⟨s⟩
    refine ⟨s.left ≫ pullback.fst E.gluedSchemeToBase f, ?_⟩
    rw [Category.assoc, pullback.condition, ← Category.assoc]
    have hs : s.left ≫ pullback.snd E.gluedSchemeToBase f = 𝟙 X :=
      MorphismProperty.Over.w s
    rw [hs, Category.id_comp]
  · rintro ⟨s, hs⟩
    let a : X ⟶ pullback E.gluedSchemeToBase f :=
      pullback.lift s (𝟙 X) (hs.trans (Category.id_comp f).symm)
    refine ⟨MorphismProperty.Over.homMk a ?_⟩
    exact pullback.lift_snd _ _ _

end

end OAI.AlgebraicGeometry.FormalGeometry.Completion.FiniteTorsor

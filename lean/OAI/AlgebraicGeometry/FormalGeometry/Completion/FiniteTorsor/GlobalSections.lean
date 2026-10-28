import OAI.AlgebraicGeometry.FormalGeometry.Completion.FiniteTorsor.GlobalScheme
import OAI.AlgebraicGeometry.FormalGeometry.Completion.RepresentableSlice

/-! # Global Sections -/

namespace OAI.AlgebraicGeometry.FormalGeometry.Completion.FiniteTorsor

noncomputable section

/-!
# Completion: global sections and geometric trivializations of actual torsors

Vanishing of the original cohomology class is equivalent to a section of
its actual finite étale scheme. A local torsor section identifies the
restriction of that global representative with the explicit constant cover.
-/

open _root_.CategoryTheory Limits _root_.AlgebraicGeometry Opposite

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

universe u

/-- The identity scheme is a terminal object in its actual pro-étale site. -/
def GlobalSections.Construction.proEtaleIdentityIsTerminal (X : Scheme.{u}) : IsTerminal (Scheme.ProEt.mk (𝟙 X)) :=
  IsTerminal.ofUniqueHom
    (fun U => MorphismProperty.Over.homMk U.hom (Category.comp_id _))
    (fun U f => MorphismProperty.Over.Hom.ext (by
      exact (Category.comp_id f.left).symm.trans (MorphismProperty.Over.w f)))

variable {X : Scheme.{u}} {ℓ n : ℕ} [NeZero (ℓ ^ n)]
  (E : App.Construction.FiniteCoefficientExtension ℓ n X)

/-- The actual scheme representative has a section precisely when its cohomology class vanishes. -/
theorem App.Construction.FiniteCoefficientExtension.class_eq_zero_iff_scheme_section :
    E.extClass = 0 ↔ ∃ s : X ⟶ E.gluedScheme, s ≫ E.gluedSchemeToBase = 𝟙 X := by
  rw [E.class_eq_zero_iff_fiber_nonempty]
  let e := (GlobalSections.Construction.proEtaleIdentityIsTerminal X).uniqueUpToIso terminalIsTerminal
  constructor
  · rintro ⟨s⟩
    let f := e.hom ≫ E.gluedRepresentative.homEquiv.symm s
    exact ⟨f.left, MorphismProperty.Over.w f⟩
  · rintro ⟨s, hs⟩
    let f : Scheme.ProEt.mk (𝟙 X) ⟶ E.gluedProEt := MorphismProperty.Over.homMk s hs
    exact ⟨E.gluedRepresentative.homEquiv (e.inv ≫ f)⟩

/-- A local section trivializes the actual global representative in the corresponding slice. -/
def App.Construction.FiniteCoefficientExtension.gluedTrivialization (U : X.ProEt) (s : E.Fiber U) :
    Over.mk (prod.snd : E.gluedProEt ⨯ U ⟶ U) ≅ Local.Construction.finiteCoefficientSlice ℓ n U :=
  (RepresentableSlice.Construction.representableByOnSlice E.gluedRepresentative U).uniqueUpToIso (E.localRepresentative s)

/-- The representing object carries the universal actual torsor section. -/
def App.Construction.FiniteCoefficientExtension.gluedUniversalSection : E.Fiber E.gluedProEt :=
  E.gluedRepresentative.homEquiv (𝟙 E.gluedProEt)

/-- The representing finite étale morphism is surjective, as follows from actual local lifts. -/
theorem App.Construction.FiniteCoefficientExtension.gluedSchemeToBase_surjective : Surjective E.gluedSchemeToBase := by
  constructor
  intro x
  obtain ⟨i, y, hy⟩ := X.directedAffineCover.exists_eq x
  let U := (GluingData.Construction.proEtaleDirectedAffineDiagram X).obj i
  obtain ⟨V, g, _, hg, ⟨s⟩⟩ := E.exists_affine_cover_lift U
  obtain ⟨z, hz⟩ := g.left.surjective y
  let a : V ⟶ E.gluedProEt := E.gluedRepresentative.homEquiv.symm s
  refine ⟨a.left z, ?_⟩
  calc
    E.gluedSchemeToBase (a.left z) = V.hom z :=
      congrArg (fun f : V.left ⟶ X => f z) (MorphismProperty.Over.w a)
    _ = U.hom (g.left z) :=
      (congrArg (fun f : V.left ⟶ X => f z) (MorphismProperty.Over.w g)).symm
    _ = x := by rw [hz]; exact hy

/-- The self-pullback of the actual torsor is its finite constant cover. -/
def App.Construction.FiniteCoefficientExtension.gluedSelfTrivialization :
    Over.mk (prod.snd : E.gluedProEt ⨯ E.gluedProEt ⟶ E.gluedProEt) ≅
      Local.Construction.finiteCoefficientSlice ℓ n E.gluedProEt :=
  E.gluedTrivialization E.gluedProEt E.gluedUniversalSection

end

end OAI.AlgebraicGeometry.FormalGeometry.Completion.FiniteTorsor

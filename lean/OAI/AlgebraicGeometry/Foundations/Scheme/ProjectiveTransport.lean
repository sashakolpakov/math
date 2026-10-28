import OAI.AlgebraicGeometry.Foundations.Scheme.SmoothProjective

/-! # Projective Transport -/

namespace OAI.AlgebraicGeometry.Foundations.Scheme

noncomputable section

/-!
# Transport of actual projective presentations

The constructions here precompose genuine scheme morphisms with scheme
isomorphisms. The resulting presentations have the transported complex
structure map, and define isomorphic objects over `Spec ℂ`.
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry

/-- Precomposing by a scheme isomorphism preserves and reflects smoothness. -/
theorem ProjectiveTransport.smooth_precompose_iso_iff {X Y S : Scheme}
    (e : Y ≅ X) (f : X ⟶ S) : Smooth (e.hom ≫ f) ↔ Smooth f := by
  constructor
  · intro h
    let : Smooth (e.hom ≫ f) := h
    have h' : Smooth (e.inv ≫ (e.hom ≫ f)) := inferInstance
    simpa using h'
  · intro h
    let : Smooth f := h
    infer_instance

/-- Precomposing by a scheme isomorphism preserves and reflects closed immersions. -/
theorem ProjectiveTransport.closedImmersion_precompose_iso_iff {X Y S : Scheme}
    (e : Y ≅ X) (f : X ⟶ S) :
    IsClosedImmersion (e.hom ≫ f) ↔ IsClosedImmersion f := by
  constructor
  · intro h
    let : IsClosedImmersion (e.hom ≫ f) := h
    have h' : IsClosedImmersion (e.inv ≫ (e.hom ≫ f)) := inferInstance
    simpa using h'
  · intro h
    let : IsClosedImmersion f := h
    infer_instance

section

variable {X Y : Scheme} {f : X ⟶ ProjectiveSpace.complexBase}

/-- Transport a chosen closed projective embedding to an isomorphic scheme. -/
def SmoothProjective.ProjectivePresentation.transportIso (P : SmoothProjective.ProjectivePresentation X f) (e : Y ≅ X) :
    SmoothProjective.ProjectivePresentation Y (e.hom ≫ f) where
  ambientDimension := P.ambientDimension
  embedding := e.hom ≫ P.embedding
  closedImmersion := inferInstance
  over_base := by simp only [Category.assoc, P.over_base]

@[simp]
theorem SmoothProjective.ProjectivePresentation.transportIso_ambientDimension (P : SmoothProjective.ProjectivePresentation X f) (e : Y ≅ X) :
    (P.transportIso e).ambientDimension = P.ambientDimension := rfl

@[simp]
theorem SmoothProjective.ProjectivePresentation.transportIso_embedding (P : SmoothProjective.ProjectivePresentation X f) (e : Y ≅ X) :
    (P.transportIso e).embedding = e.hom ≫ P.embedding := rfl

/-- Existence of a projective presentation is invariant under a scheme
isomorphism, with its induced complex structure map. -/
theorem SmoothProjective.ProjectivePresentation.nonempty_transportIso_iff (e : Y ≅ X) :
    Nonempty (SmoothProjective.ProjectivePresentation Y (e.hom ≫ f)) ↔
      Nonempty (SmoothProjective.ProjectivePresentation X f) := by
  constructor
  · rintro ⟨P⟩
    have h : Nonempty (SmoothProjective.ProjectivePresentation X (e.inv ≫ (e.hom ≫ f))) :=
      ⟨P.transportIso e.symm⟩
    simpa using h
  · rintro ⟨P⟩
    exact ⟨P.transportIso e⟩

/-- The same invariance for explicitly specified maps to `Spec ℂ`. -/
theorem SmoothProjective.ProjectivePresentation.nonempty_iff_of_iso {g : Y ⟶ ProjectiveSpace.complexBase}
    (e : Y ≅ X) (h : e.hom ≫ f = g) :
    Nonempty (SmoothProjective.ProjectivePresentation Y g) ↔
      Nonempty (SmoothProjective.ProjectivePresentation X f) := by
  subst g
  exact SmoothProjective.ProjectivePresentation.nonempty_transportIso_iff e

end

/-- Transport a smooth projective complex scheme and its presentation along
an isomorphism of its underlying scheme. -/
def SmoothProjective.SmoothProjectivePresentation.transportIso (P : SmoothProjective.SmoothProjectivePresentation) {Y : Scheme}
    (e : Y ≅ P.carrier) : SmoothProjective.SmoothProjectivePresentation where
  carrier := Y
  structureMap := e.hom ≫ P.structureMap
  projective := P.projective.transportIso e
  smooth := inferInstance

@[simp]
theorem SmoothProjective.SmoothProjectivePresentation.transportIso_structureMap (P : SmoothProjective.SmoothProjectivePresentation) {Y : Scheme}
    (e : Y ≅ P.carrier) :
    (P.transportIso e).structureMap = e.hom ≫ P.structureMap := rfl

@[simp]
theorem SmoothProjective.SmoothProjectivePresentation.transportIso_embedding (P : SmoothProjective.SmoothProjectivePresentation) {Y : Scheme}
    (e : Y ≅ P.carrier) :
    (P.transportIso e).embedding = e.hom ≫ P.embedding := rfl

/-- Transport changes the presentation but preserves the complex scheme up to
an actual isomorphism over the base. -/
def SmoothProjective.SmoothProjectivePresentation.transportIso_overIso (P : SmoothProjective.SmoothProjectivePresentation) {Y : Scheme}
    (e : Y ≅ P.carrier) : (P.transportIso e).toOver ≅ P.toOver :=
  Over.isoMk e rfl

end

end OAI.AlgebraicGeometry.Foundations.Scheme

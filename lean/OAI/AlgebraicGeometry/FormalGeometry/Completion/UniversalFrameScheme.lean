import OAI.AlgebraicGeometry.FormalGeometry.Completion.UniversalFrameOpen

/-! # Universal Frame Scheme -/

namespace OAI.AlgebraicGeometry.FormalGeometry.Completion

noncomputable section

/-! The universal frame locus is an actual open scheme. A test morphism
factors through it uniquely exactly when the pulled-back universal
section is an isomorphism of line bundles. -/

set_option backward.isDefEq.respectTransparency false

open _root_.AlgebraicGeometry _root_.CategoryTheory _root_.CategoryTheory.Limits

universe u
variable {X S : Scheme.{u}} [IsAffine S] {π : X ⟶ S} [IsProper π] {L : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle X}
  (D : Geometric.SectionAlgebra.Construction.GeometricSectionAlgebraRepresentation π L.sheaf)

def Geometric.SectionAlgebra.Construction.GeometricSectionAlgebraRepresentation.frameScheme : Over D.scheme.left := Over.mk D.frameOpen.ι

instance Geometric.SectionAlgebra.Construction.GeometricSectionAlgebraRepresentation.frameScheme_openImmersion : IsOpenImmersion D.frameScheme.hom :=
  inferInstanceAs (IsOpenImmersion D.frameOpen.ι)

def Geometric.SectionAlgebra.Construction.GeometricSectionAlgebraRepresentation.frameSchemeOverBase : Over S := Over.mk (D.frameOpen.ι ≫ D.scheme.hom)

instance Geometric.SectionAlgebra.Construction.GeometricSectionAlgebraRepresentation.frameScheme_locallyOfFiniteType : LocallyOfFiniteType D.frameSchemeOverBase.hom :=
  inferInstanceAs (LocallyOfFiniteType (D.frameOpen.ι ≫ D.scheme.hom))

theorem Geometric.SectionAlgebra.Construction.GeometricSectionAlgebraRepresentation.frameScheme_lift_unique {T : Scheme.{u}} (t : T ⟶ D.scheme.left)
    (a b : Over.mk t ⟶ D.frameScheme) : a = b := by
  apply Over.OverMorphism.ext
  apply (cancel_mono D.frameScheme.hom).mp
  exact a.w.trans b.w.symm

theorem Geometric.SectionAlgebra.Construction.GeometricSectionAlgebraRepresentation.frameScheme_hasLift_iff {Z T : Scheme.{u}}
    (j : Z ⟶ D.universalFamily) (τ : Z ⟶ T) (t : T ⟶ D.scheme.left)
    (hp : IsPullback j τ (pullback.snd π D.scheme.hom) t) :
    Nonempty (Over.mk t ⟶ D.frameScheme) ↔ IsIso (AbelianModuli.HilbertConstruction.Ample.LineBundles.pullbackSection j D.universalSectionHom) := by
  rw [D.universalSectionHom_isIso_iff j τ t hp]
  constructor
  · rintro ⟨a⟩ y
    have hy : D.frameOpen.ι (a.left y) = t y := congrArg (fun f : T ⟶ D.scheme.left => f y) a.w
    exact hy ▸ (a.left y).property
  · intro h
    have hr : Set.range t ⊆ Set.range D.frameOpen.ι := by
      rintro _ ⟨y, rfl⟩
      exact ⟨⟨t y, h y⟩, rfl⟩
    exact ⟨Over.homMk (IsOpenImmersion.lift D.frameOpen.ι t hr)
      (IsOpenImmersion.lift_fac D.frameOpen.ι t hr)⟩

end

end OAI.AlgebraicGeometry.FormalGeometry.Completion

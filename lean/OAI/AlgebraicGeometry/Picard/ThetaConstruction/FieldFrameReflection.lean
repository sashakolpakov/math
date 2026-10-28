import OAI.AlgebraicGeometry.Picard.ThetaConstruction.RelativeFrameClassification
import OAI.RepresentationTheory.Theta.Geometric.SpecLocalRings
import Mathlib.AlgebraicGeometry.Morphisms.FlatMono

/-! # Field Frame Reflection -/

namespace OAI.AlgebraicGeometry.Picard.ThetaConstruction.FieldFrameReflection.Geometric

noncomputable section

/-! A normalized projective line over a field is trivial whenever it
has a frame after a nonempty base change. The actual frame functor is
monomorphic, and its nonempty scheme is faithfully flat over the field. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

universe u
variable {K : Type u} [Field K] {X : Over (Spec (.of K))}
    [IsProper X.hom] [Smooth X.hom] [GeometricallyConnected X.hom]
    (P : AbelianModuli.HilbertConstruction.Projective.ProjectivePresentations.ProjectivePresentation X) (s : Spec (.of K) ⟶ X.left) (hs : s ≫ X.hom = 𝟙 _)
    (L : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle X.left)
    (r : (Scheme.Modules.pullback s).obj L.sheaf ≅ AbelianModuli.HilbertConstruction.Line.Bundles.structureModule (Spec (.of K)))

local instance : IsNoetherianRing Γ(Spec (.of K), ⊤) := RepresentationTheory.Theta.Geometric.SpecLocalRings.specGlobal_isNoetherianRing K

include P in
theorem field_rigidifiedFrame_isIso_of_nonempty
    (D : FormalGeometry.Completion.Geometric.SectionAlgebra.Construction.GeometricSectionAlgebraRepresentation X.hom L.sheaf)
    [Nonempty (D.rigidifiedFrameScheme s hs r).left] :
    IsIso (D.rigidifiedFrameScheme s hs r).hom := by
  let : Mono (D.rigidifiedFrameScheme s hs r).hom :=
    RelativeFrameRigidity.Geometric.relativeProjective_rigidifiedFrame_mono P s hs D r
  let : Surjective (D.rigidifiedFrameScheme s hs r).hom := by
    constructor
    intro y
    exact ⟨Classical.arbitrary _, Subsingleton.elim _ y⟩
  exact Flat.isIso_of_surjective_of_mono _

include P s hs r in
theorem field_line_trivial_of_cartesian_trivial
    {Y T : Scheme.{u}} [Nonempty T] (f : Y ⟶ X.left) (ρ : Y ⟶ T)
    (b : T ⟶ Spec (.of K)) (hp : IsPullback f ρ X.hom b)
    (e : (Scheme.Modules.pullback f).obj L.sheaf ≅ AbelianModuli.HilbertConstruction.Line.Bundles.structureModule Y) :
    Nonempty (L.sheaf ≅ AbelianModuli.HilbertConstruction.Line.Bundles.structureModule X.left) := by
  let D := FormalGeometry.Completion.Projective.LineBundleSectionScheme.Construction.projectiveLineBundleSectionModel X P L
  obtain ⟨q⟩ := RelativeFrameClassification.Geometric.relativeProjective_rigidifiedFrame_hasPoint_of_trivialization P s hs D r
    f ρ b hp e.symm
  let : Nonempty (D.rigidifiedFrameScheme s hs r).left :=
    ⟨q.left (Classical.arbitrary T)⟩
  let := field_rigidifiedFrame_isIso_of_nonempty P s hs L r D
  let a : Over.mk (𝟙 (Spec (.of K))) ⟶ D.rigidifiedFrameScheme s hs r :=
    Over.homMk (inv (D.rigidifiedFrameScheme s hs r).hom) (IsIso.inv_hom_id _)
  have hc := (RelativeFrameClassification.Geometric.relativeProjective_rigidifiedFrame_hasPoint_iff_trivialClass P s hs D r
    (𝟙 X.left) X.hom (𝟙 _) IsPullback.of_id_fst).mp ⟨a⟩
  rw [AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass_id] at hc
  exact Quotient.exact hc

end

end OAI.AlgebraicGeometry.Picard.ThetaConstruction.FieldFrameReflection.Geometric

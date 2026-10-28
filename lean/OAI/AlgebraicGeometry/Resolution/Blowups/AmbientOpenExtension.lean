import OAI.AlgebraicGeometry.Resolution.Blowups.ResolutionGeometry

/-! # Ambient Open Extension -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups.AmbientOpenExtension.Construction

noncomputable section

/-! An explicit ambient extension of an open subset of a closed subscheme. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

def closedImmersionAmbientOpen {Z X : Scheme.{u}} (i : Z ⟶ X)
    [IsClosedImmersion i] (V : Z.Opens) : X.Opens :=
  ⟨(i '' (V : Set Z)ᶜ)ᶜ, (i.isClosedEmbedding.isClosedMap _ V.isOpen.isClosed_compl).isOpen_compl⟩

theorem closedImmersionAmbientOpen_preimage {Z X : Scheme.{u}} (i : Z ⟶ X)
    [IsClosedImmersion i] (V : Z.Opens) : i ⁻¹ᵁ closedImmersionAmbientOpen i V = V := by
  apply TopologicalSpace.Opens.ext
  change i ⁻¹' (i '' (V : Set Z)ᶜ)ᶜ = (V : Set Z)
  rw [Set.preimage_compl, Set.preimage_image_eq _ i.isClosedEmbedding.injective, compl_compl]

theorem closedImmersionAmbientOpen_contains_complement {Z X : Scheme.{u}} (i : Z ⟶ X)
    [IsClosedImmersion i] (V : Z.Opens) :
    (Set.range i)ᶜ ⊆ (closedImmersionAmbientOpen i V : Set X) := by
  intro x hx hbad
  exact hx (Set.image_subset_range i _ hbad)

def projectiveSmoothAmbientOpen {Z : Scheme} (f : Z ⟶ Foundations.Scheme.ProjectiveSpace.complexBase)
    (P : Foundations.Scheme.SmoothProjective.ProjectivePresentation Z f) : (Foundations.Scheme.ProjectiveSpace.projectiveSpace P.ambientDimension).Opens := by
  let : LocallyOfFinitePresentation f := P.locallyOfFinitePresentation
  let : IsClosedImmersion P.embedding := P.closedImmersion
  exact closedImmersionAmbientOpen P.embedding f.smoothLocus

theorem projectiveSmoothAmbientOpen_preimage {Z : Scheme} (f : Z ⟶ Foundations.Scheme.ProjectiveSpace.complexBase)
    (P : Foundations.Scheme.SmoothProjective.ProjectivePresentation Z f) :
    letI : LocallyOfFinitePresentation f := P.locallyOfFinitePresentation
    P.embedding ⁻¹ᵁ projectiveSmoothAmbientOpen f P = f.smoothLocus := by
  let : LocallyOfFinitePresentation f := P.locallyOfFinitePresentation
  let : IsClosedImmersion P.embedding := P.closedImmersion
  exact closedImmersionAmbientOpen_preimage P.embedding f.smoothLocus

end

end OAI.AlgebraicGeometry.Resolution.Blowups.AmbientOpenExtension.Construction

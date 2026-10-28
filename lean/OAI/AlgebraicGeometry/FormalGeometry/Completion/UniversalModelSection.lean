import OAI.AlgebraicGeometry.FormalGeometry.Completion.Geometric.SectionScheme

/-! # Universal Model Section -/

namespace OAI.AlgebraicGeometry.FormalGeometry.Completion

noncomputable section

/-! The section corresponding to the identity of the representing
scheme is universal under the actual geometric pullback operation. -/

set_option backward.isDefEq.respectTransparency false

open _root_.AlgebraicGeometry _root_.CategoryTheory _root_.CategoryTheory.Limits Opposite
open _root_.AlgebraicGeometry.Scheme.Modules

universe u
variable {X S : Scheme.{u}} [IsAffine S] {π : X ⟶ S} {M : X.Modules}
  (D : Geometric.SectionAlgebra.Construction.GeometricSectionAlgebraRepresentation π M)

abbrev Geometric.SectionAlgebra.Construction.GeometricSectionAlgebraRepresentation.universalFamily : Scheme.{u} := pullback π D.scheme.hom

def Geometric.SectionAlgebra.Construction.GeometricSectionAlgebraRepresentation.universalSection : Γ((Scheme.Modules.pullback (pullback.fst π D.scheme.hom)).obj M, ⊤) :=
  (D.sectionPointEquiv (pullback.fst π D.scheme.hom) (pullback.snd π D.scheme.hom) D.scheme.hom
    (IsPullback.of_hasPullback π D.scheme.hom)).symm (𝟙 D.scheme)

theorem Geometric.SectionAlgebra.Construction.GeometricSectionAlgebraRepresentation.universalSection_classifies :
    D.sectionPointEquiv (pullback.fst π D.scheme.hom) (pullback.snd π D.scheme.hom) D.scheme.hom
      (IsPullback.of_hasPullback π D.scheme.hom) D.universalSection = 𝟙 D.scheme :=
  (D.sectionPointEquiv (pullback.fst π D.scheme.hom) (pullback.snd π D.scheme.hom) D.scheme.hom
    (IsPullback.of_hasPullback π D.scheme.hom)).apply_symm_apply _

theorem Geometric.SectionAlgebra.Construction.GeometricSectionAlgebraRepresentation.universalSection_pullback_classifies {Z T : Scheme.{u}} [IsAffine T]
    (j : Z ⟶ D.universalFamily) (τ : Z ⟶ T) (t : T ⟶ D.scheme.left)
    (hj : j ≫ pullback.snd π D.scheme.hom = τ ≫ t)
    (ho : IsPullback (j ≫ pullback.fst π D.scheme.hom) τ π (t ≫ D.scheme.hom)) :
    D.sectionPointEquiv (j ≫ pullback.fst π D.scheme.hom) τ (t ≫ D.scheme.hom) ho
      (GlobalSectionComposition.Construction.globalSectionCompositePullback (pullback.fst π D.scheme.hom) j M D.universalSection) =
      (Over.homMk t rfl : Over.mk (t ≫ D.scheme.hom) ⟶ D.scheme) := by
  have hn := D.sectionPointEquiv_natural (pullback.fst π D.scheme.hom) j
    (pullback.snd π D.scheme.hom) τ D.scheme.hom t (IsPullback.of_hasPullback π D.scheme.hom)
      hj ho D.universalSection
  rw [D.universalSection_classifies] at hn
  exact hn.trans (Category.comp_id (Over.homMk t rfl : Over.mk (t ≫ D.scheme.hom) ⟶ D.scheme))

end

end OAI.AlgebraicGeometry.FormalGeometry.Completion

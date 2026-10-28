import OAI.AlgebraicGeometry.FormalGeometry.Completion.UniversalFrameScheme

/-! # Line Bundle Section Scheme -/

namespace OAI.AlgebraicGeometry.FormalGeometry.Completion.Projective.LineBundleSectionScheme

noncomputable section

/-! Native section and frame schemes of a flat projective line-bundle
family over an affine Noetherian base. Their finite model and all
classification maps are constructed from the projective presentation. -/

set_option backward.isDefEq.respectTransparency false

open _root_.AlgebraicGeometry _root_.CategoryTheory _root_.CategoryTheory.Limits Opposite
open _root_.AlgebraicGeometry.Scheme.Modules

namespace Construction

universe u
variable {S : Scheme.{u}} [IsAffine S] [IsNoetherianRing Γ(S, ⊤)]
  (X : Over S) (P : AbelianModuli.HilbertConstruction.Projective.ProjectivePresentations.ProjectivePresentation X) [Flat X.hom] (L : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle X.left)

def projectiveLineBundleSectionModel : Geometric.SectionAlgebra.Construction.GeometricSectionAlgebraRepresentation X.hom L.sheaf :=
  Classical.choice (Geometric.SectionAlgebra.Construction.projectiveLineBundle_sectionAlgebraRepresentation X P L)

def projectiveLineBundleSectionScheme : Over S := (projectiveLineBundleSectionModel X P L).scheme

instance projectiveLineBundleSectionScheme_isAffine : IsAffine (projectiveLineBundleSectionScheme X P L).left :=
  inferInstanceAs (IsAffine (projectiveLineBundleSectionModel X P L).scheme.left)

instance projectiveLineBundleSectionScheme_locallyOfFiniteType :
    LocallyOfFiniteType (projectiveLineBundleSectionScheme X P L).hom :=
  inferInstanceAs (LocallyOfFiniteType (projectiveLineBundleSectionModel X P L).scheme.hom)

instance projectiveLineBundleSectionScheme_quasiCompact :
    QuasiCompact (projectiveLineBundleSectionScheme X P L).hom :=
  inferInstanceAs (QuasiCompact (projectiveLineBundleSectionModel X P L).scheme.hom)

def projectiveLineBundleSectionPointEquiv {Y T : Scheme.{u}} [IsAffine T]
    (f : Y ⟶ X.left) (ρ : Y ⟶ T) (g : T ⟶ S) (hp : IsPullback f ρ X.hom g) :
    (SheafCohomology.Cech.SchemeModuleBaseBasic.Scheme.Modules.baseModulePresheaf ρ ((Scheme.Modules.pullback f).obj L.sheaf)).obj (op ⊤) ≃
      (Over.mk g ⟶ projectiveLineBundleSectionScheme X P L) :=
  (projectiveLineBundleSectionModel X P L).sectionPointEquiv f ρ g hp

theorem projectiveLineBundleSectionPointEquiv_natural {Y Z T T' : Scheme.{u}} [IsAffine T] [IsAffine T']
    (f : Y ⟶ X.left) (j : Z ⟶ Y) (ρ : Y ⟶ T) (τ : Z ⟶ T') (g : T ⟶ S) (t : T' ⟶ T)
    (hp : IsPullback f ρ X.hom g) (hj : j ≫ ρ = τ ≫ t) (ho : IsPullback (j ≫ f) τ X.hom (t ≫ g))
    (s : (SheafCohomology.Cech.SchemeModuleBaseBasic.Scheme.Modules.baseModulePresheaf ρ ((Scheme.Modules.pullback f).obj L.sheaf)).obj (op ⊤)) :
    projectiveLineBundleSectionPointEquiv X P L (j ≫ f) τ (t ≫ g) ho
      (GlobalSectionComposition.Construction.globalSectionCompositePullback f j L.sheaf s) =
      (Over.homMk t rfl : Over.mk (t ≫ g) ⟶ Over.mk g) ≫ projectiveLineBundleSectionPointEquiv X P L f ρ g hp s :=
  (projectiveLineBundleSectionModel X P L).sectionPointEquiv_natural f j ρ τ g t hp hj ho s

def projectiveLineBundleFrameScheme : Over S := by
  haveI : IsProper X.hom := P.proper
  exact (projectiveLineBundleSectionModel X P L).frameSchemeOverBase

instance projectiveLineBundleFrameScheme_locallyOfFiniteType :
    LocallyOfFiniteType (projectiveLineBundleFrameScheme X P L).hom := by
  have : IsProper X.hom := P.proper
  exact (projectiveLineBundleSectionModel X P L).frameScheme_locallyOfFiniteType

end Construction

end

end OAI.AlgebraicGeometry.FormalGeometry.Completion.Projective.LineBundleSectionScheme

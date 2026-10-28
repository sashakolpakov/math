import OAI.AlgebraicGeometry.FormalGeometry.Completion.UniversalModelSection

/-! # Classified Section Pullback -/

namespace OAI.AlgebraicGeometry.FormalGeometry.Completion

noncomputable section

/-! Pull back the universal section along an arbitrary classifying
morphism, using the actual Cartesian comparison of the two families. -/

set_option backward.isDefEq.respectTransparency false

open _root_.AlgebraicGeometry _root_.CategoryTheory _root_.CategoryTheory.Limits Opposite
open _root_.AlgebraicGeometry.Scheme.Modules

universe u
variable {X S : Scheme.{u}} [IsAffine S] {π : X ⟶ S} {M : X.Modules}
  (D : Geometric.SectionAlgebra.Construction.GeometricSectionAlgebraRepresentation π M)

theorem Geometric.SectionAlgebra.Construction.GeometricSectionAlgebraRepresentation.sectionPointEquiv_top_congr {Y T : Scheme.{u}} [IsAffine T]
    (f f' : Y ⟶ X) (hf : f = f') (ρ : Y ⟶ T) (g : T ⟶ S)
    (hp : IsPullback f ρ π g) (hp' : IsPullback f' ρ π g)
    (s : Γ((Scheme.Modules.pullback f).obj M, ⊤)) :
    D.sectionPointEquiv f' ρ g hp' (((Scheme.Modules.pullbackCongr hf).hom.app M).app ⊤ s) =
      D.sectionPointEquiv f ρ g hp s := by
  subst f'
  rfl

theorem Geometric.SectionAlgebra.Construction.GeometricSectionAlgebraRepresentation.sectionPointEquiv_base_congr_left {Y T : Scheme.{u}} [IsAffine T]
    (f : Y ⟶ X) (ρ : Y ⟶ T) (g g' : T ⟶ S) (hg : g = g')
    (hp : IsPullback f ρ π g) (hp' : IsPullback f ρ π g')
    (s : Γ((Scheme.Modules.pullback f).obj M, ⊤)) :
    (D.sectionPointEquiv f ρ g' hp' s).left = (D.sectionPointEquiv f ρ g hp s).left := by
  subst g'
  rfl

variable {Y T : Scheme.{u}} (f : Y ⟶ X) (ρ : Y ⟶ T) (g : T ⟶ S)
  (hp : IsPullback f ρ π g) (p : Over.mk g ⟶ D.scheme)

def Geometric.SectionAlgebra.Construction.GeometricSectionAlgebraRepresentation.classifierFamilyMap : Y ⟶ D.universalFamily :=
  pullback.lift f (ρ ≫ p.left) (by rw [Category.assoc, p.w]; exact hp.w)

theorem Geometric.SectionAlgebra.Construction.GeometricSectionAlgebraRepresentation.classifierFamilyMap_fst : D.classifierFamilyMap f ρ g hp p ≫ pullback.fst π D.scheme.hom = f :=
  pullback.lift_fst _ _ _

theorem Geometric.SectionAlgebra.Construction.GeometricSectionAlgebraRepresentation.classifierFamilyMap_snd : D.classifierFamilyMap f ρ g hp p ≫ pullback.snd π D.scheme.hom = ρ ≫ p.left :=
  pullback.lift_snd _ _ _

theorem Geometric.SectionAlgebra.Construction.GeometricSectionAlgebraRepresentation.classifierFamilyMap_isPullback :
    IsPullback (D.classifierFamilyMap f ρ g hp p) ρ (pullback.snd π D.scheme.hom) p.left := by
  refine IsPullback.of_right (t := IsPullback.of_hasPullback π D.scheme.hom) ?_
    (D.classifierFamilyMap_snd f ρ g hp p)
  rw [D.classifierFamilyMap_fst, p.w]
  exact hp

def Geometric.SectionAlgebra.Construction.GeometricSectionAlgebraRepresentation.classifiedSectionPullback : Γ((Scheme.Modules.pullback f).obj M, ⊤) :=
  (((Scheme.Modules.pullbackCongr (D.classifierFamilyMap_fst f ρ g hp p)).hom.app M).app ⊤)
    (GlobalSectionComposition.Construction.globalSectionCompositePullback (pullback.fst π D.scheme.hom)
      (D.classifierFamilyMap f ρ g hp p) M D.universalSection)

theorem Geometric.SectionAlgebra.Construction.GeometricSectionAlgebraRepresentation.classifiedSectionPullback_classifies [IsAffine T] :
    D.sectionPointEquiv f ρ g hp (D.classifiedSectionPullback f ρ g hp p) = p := by
  let j := D.classifierFamilyMap f ρ g hp p
  have hf := D.classifierFamilyMap_fst f ρ g hp p
  have hj := D.classifierFamilyMap_snd f ρ g hp p
  have ho := (D.classifierFamilyMap_isPullback f ρ g hp p).paste_horiz
    (IsPullback.of_hasPullback π D.scheme.hom)
  have hp' : IsPullback f ρ π (p.left ≫ D.scheme.hom) := by rw [p.w]; exact hp
  have hc := D.universalSection_pullback_classifies j ρ p.left hj ho
  have ht := D.sectionPointEquiv_top_congr (j ≫ pullback.fst π D.scheme.hom) f hf ρ
    (p.left ≫ D.scheme.hom) ho hp'
    (GlobalSectionComposition.Construction.globalSectionCompositePullback (pullback.fst π D.scheme.hom) j M D.universalSection)
  have hb := D.sectionPointEquiv_base_congr_left f ρ (p.left ≫ D.scheme.hom) g p.w hp' hp
    (D.classifiedSectionPullback f ρ g hp p)
  apply Over.OverMorphism.ext
  exact hb.trans ((congrArg Over.Hom.left ht).trans (congrArg Over.Hom.left hc))

theorem Geometric.SectionAlgebra.Construction.GeometricSectionAlgebraRepresentation.classifiedSectionPullback_recovers [IsAffine T]
    (s : (SheafCohomology.Cech.SchemeModuleBaseBasic.Scheme.Modules.baseModulePresheaf ρ ((Scheme.Modules.pullback f).obj M)).obj (op ⊤)) :
    D.classifiedSectionPullback f ρ g hp (D.sectionPointEquiv f ρ g hp s) = s :=
  (D.sectionPointEquiv f ρ g hp).injective
    (D.classifiedSectionPullback_classifies f ρ g hp (D.sectionPointEquiv f ρ g hp s))

end

end OAI.AlgebraicGeometry.FormalGeometry.Completion

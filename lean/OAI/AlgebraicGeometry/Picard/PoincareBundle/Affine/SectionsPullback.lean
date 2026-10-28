import OAI.AlgebraicGeometry.Picard.PoincareBundle.Affine.QuasiCoherent
import OAI.AlgebraicGeometry.Picard.PoincareBundle.QuasiCoherent

/-! # Sections Pullback -/

namespace OAI.AlgebraicGeometry.Picard.PoincareBundle.Affine.SectionsPullback

noncomputable section

/-!
# Global sections of affine pullback for PoincareBundle

The comparison is a natural isomorphism of actual affine module and
quasi-coherent-sheaf functors, transported through the proved tilde equivalences.
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

open OAI.AlgebraicGeometry.Picard.PoincareBundle.Affine.QuasiCoherent

variable {R S : CommRingCat.{u}}

/-- Taking global sections commutes with affine pullback and extension of scalars. -/
def sectionsPullbackIso (f : R ⟶ S) :
    (tildeEquiv (R := R)).inverse ⋙ ModuleCat.extendScalars f.hom ≅
      QuasiCoherent.pullback f ⋙ (tildeEquiv (R := S)).inverse :=
  (Functor.isoWhiskerRight (QuasiCoherent.pullbackModuleModelIso f) (tildeEquiv (R := S)).inverse ≪≫
    Functor.associator (tildeEquiv (R := R)).inverse
      (ModuleCat.extendScalars f.hom ⋙ (tildeEquiv (R := S)).functor)
      (tildeEquiv (R := S)).inverse ≪≫
    Functor.isoWhiskerLeft (tildeEquiv (R := R)).inverse
      (Functor.associator (ModuleCat.extendScalars f.hom) (tildeEquiv (R := S)).functor
        (tildeEquiv (R := S)).inverse) ≪≫
    Functor.isoWhiskerLeft (tildeEquiv (R := R)).inverse
      (Functor.isoWhiskerLeft (ModuleCat.extendScalars f.hom) (tildeEquiv (R := S)).unitIso.symm) ≪≫
    Functor.isoWhiskerLeft (tildeEquiv (R := R)).inverse
      (Functor.rightUnitor (ModuleCat.extendScalars f.hom))).symm

/-- The natural comparison for a quasi-coherent sheaf on an affine scheme. -/
def globalSectionsPullbackIso (f : R ⟶ S) (M : (Spec R).Modules) [M.IsQuasicoherent] :
    (ModuleCat.extendScalars f.hom).obj ((moduleSpecΓFunctor (R := R)).obj M) ≅
      (moduleSpecΓFunctor (R := S)).obj ((Scheme.Modules.pullback (Spec.map f)).obj M) :=
  (sectionsPullbackIso f).app ⟨M, inferInstance⟩

/-- Every actual sheaf morphism commutes with the affine global-sections comparison. -/
theorem globalSectionsPullbackIso_naturality (f : R ⟶ S) {M N : (Spec R).Modules}
    [M.IsQuasicoherent] [N.IsQuasicoherent] (a : M ⟶ N) :
    (ModuleCat.extendScalars f.hom).map ((moduleSpecΓFunctor (R := R)).map a) ≫
        (globalSectionsPullbackIso f N).hom =
      (globalSectionsPullbackIso f M).hom ≫
        (moduleSpecΓFunctor (R := S)).map ((Scheme.Modules.pullback (Spec.map f)).map a) :=
  (sectionsPullbackIso f).hom.naturality
    (show (⟨M, inferInstance⟩ : QuasiCoherent.QCSheaves R) ⟶ ⟨N, inferInstance⟩ from ObjectProperty.homMk a)

/-- In particular, the comparison applies to the actual geometric line bundles used in PoincareBundle. -/
def lineSectionsPullbackIso (f : R ⟶ S) (L : Line.Bundles.LineBundle (Spec R)) :
    (ModuleCat.extendScalars f.hom).obj ((moduleSpecΓFunctor (R := R)).obj L.sheaf) ≅
      (moduleSpecΓFunctor (R := S)).obj
        ((Line.Bundles.LineBundle.pullback (Spec.map f) L).sheaf) :=
  globalSectionsPullbackIso f L.sheaf

end

end OAI.AlgebraicGeometry.Picard.PoincareBundle.Affine.SectionsPullback

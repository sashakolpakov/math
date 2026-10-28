import OAI.AlgebraicGeometry.PELModuli.IntegralModel.LevelPullbackFaithful
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Level.IsoPoincareDescent
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Level.IsoCalculus

/-! # Recovered Polarized Iso -/

namespace OAI.AlgebraicGeometry.PELModuli.IntegralModel.RecoveredPolarizedIso

noncomputable section

/-! Recovered actual group isomorphisms preserve the complete polarized
full-level data when their pullbacks are the specified local comparison. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj

variable {S Y : Scheme.{0}} {g N : ℕ} {δ : Fin g → ℕ}
    (A B : AbelianModuli.HilbertConstruction.PolarizationData.PolarizedAbelianWithFullLevel g δ N S) (u : Y ⟶ S)
    [Flat u] [Surjective u] [QuasiCompact u] [LocallyOfFinitePresentation u]
    (e : AbelianModuli.HilbertConstruction.Moduli.Isomorphisms.LevelPreservingIso (A.pullback u) (B.pullback u))
    (qA : A.abelian.scheme ≅ B.abelian.scheme) (qD : A.dual.abelian.scheme ≅ B.dual.abelian.scheme)
    [IsMonHom qA.hom] [IsMonHom qD.hom]
    (hA : (Over.pullback u).mapIso qA = e.abelian) (hD : (Over.pullback u).mapIso qD = e.dual)

omit [QuasiCompact u] [IsMonHom qA.hom] [IsMonHom qD.hom] in
include hA hD in
theorem recoveredIso_polarization :
    A.polarization.isogeny.hom ≫ qD.hom = qA.hom ≫ B.polarization.isogeny.hom := by
  apply (Over.pullback u).map_injective
  have ha := congrArg Iso.hom hA
  have hd := congrArg Iso.hom hD
  exact ((Over.pullback u).map_comp _ _).trans
    ((congrArg (fun z => (Over.pullback u).map A.polarization.isogeny.hom ≫ z) hd).trans
      (e.polarization.trans
        ((congrArg (fun z => z ≫ (Over.pullback u).map B.polarization.isogeny.hom) ha.symm).trans
          ((Over.pullback u).map_comp _ _).symm)))

omit [QuasiCompact u] in
include hA in
theorem recoveredIso_level : A.level.transport qA = B.level := by
  apply LevelPullbackFaithful.fullLevel_pullback_injective_of_epi B.abelian u
  apply (AbelianModuli.ReferenceFamily.Level.IsoCalculus.fullLevel_transport_pullback A.level qA u).trans
  apply AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme.FullLevel.ext_basis
  intro T c
  have he : (AbelianModuli.ReferenceFamily.Level.IsoCalculus.abelianPullbackIso qA u).hom = e.abelian.hom := congrArg Iso.hom hA
  exact (congrArg (fun z => ((A.level.pullback u).hom.app (.op T) c).val ≫ z) he).trans (e.level T c)

def recoveredPolarizedIso
    (hΓ : ∀ V : Over S, IsIso (fst V A.abelian.scheme).left.appTop) : AbelianModuli.HilbertConstruction.Moduli.Isomorphisms.LevelPreservingIso A B where
  abelian := qA
  dual := qD
  abelianGroup := inferInstance
  dualGroup := inferInstance
  polarization := recoveredIso_polarization A B u e qA qD hA hD
  poincare := AbelianModuli.ReferenceFamily.Level.IsoPoincareDescent.levelIso_poincare_descends A B u hΓ e qA.hom qD.hom
    (congrArg Iso.hom hA) (congrArg Iso.hom hD)
  level T c := congrArg
    (fun α : B.abelian.FullLevel N => (α.hom.app (.op T) c).val) (recoveredIso_level A B u e qA hA)

end

end OAI.AlgebraicGeometry.PELModuli.IntegralModel.RecoveredPolarizedIso

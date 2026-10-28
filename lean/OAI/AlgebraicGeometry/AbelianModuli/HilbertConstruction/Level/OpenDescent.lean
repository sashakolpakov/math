import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Level.UniversalFamilyRecovery
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.ParameterPullbackLevelCoherence
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Directed.FamilyHomGluing

/-! # Open Descent -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Level.OpenDescent.AbelianScheme

noncomputable section

/-! Compatible original ordered full levels glue on a Noetherian abelian
family. The proof uses the already constructed full-level parameter and
its all-test naturality; no representability input is assumed. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
universe u

namespace FullLevel
variable {S : Scheme.{u}} {g N : ℕ} {A : Abelian.Schemes.AbelianScheme g S}

theorem _root_.OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme.FullLevel.transport_pullbackId (l : A.FullLevel N) :
    (l.pullback (𝟙 S)).transport A.pullbackIdIso = l := by
  apply Abelian.Schemes.AbelianScheme.FullLevel.ext_basis
  intro T c
  apply Over.OverMorphism.ext
  exact (congrArg (fun z => ((l.pullback (𝟙 S)).hom.app (.op T) c).val.left ≫ z)
    A.pullbackIdIso_hom_left).trans
      ((congrArg (fun x : A.Points ((Over.map (𝟙 S)).obj T) => x.left)
        (l.pullback_basis (𝟙 S) T c)).trans (l.basis_mapId_left T c))

theorem _root_.OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme.FullLevel.pullback_transportId (l : (A.pullback (𝟙 S)).FullLevel N) :
    (l.transport A.pullbackIdIso).pullback (𝟙 S) = l := by
  apply Abelian.Schemes.AbelianScheme.FullLevel.transport_injective A.pullbackIdIso
  exact Abelian.Schemes.AbelianScheme.FullLevel.transport_pullbackId (l.transport A.pullbackIdIso)

end FullLevel

def _root_.OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme.openCoverParameterIso {S : Scheme.{u}} {g : ℕ} (A : Abelian.Schemes.AbelianScheme g S)
    (C : S.OpenCover.{u}) [Category C.I₀] [C.LocallyDirected]
    {i j : C.I₀} (f : i ⟶ j) :
    (A.pullback (C.f i)).scheme ≅ ((A.pullback (C.f j)).pullback (C.trans f)).scheme :=
  A.parameterPullbackIso (Directed.FamilyHomGluing.DirectedFamilyHomGluing.testMap C f)

instance _root_.OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme.openCoverParameterIso_symm_group {S : Scheme.{u}} {g : ℕ} (A : Abelian.Schemes.AbelianScheme g S)
    (C : S.OpenCover.{u}) [Category C.I₀] [C.LocallyDirected]
    {i j : C.I₀} (f : i ⟶ j) :
    IsMonHom (A.openCoverParameterIso C f).symm.hom :=
  Abelian.Schemes.AbelianScheme.parameterPullbackIso_symm_isMonHom (Directed.FamilyHomGluing.DirectedFamilyHomGluing.testMap C f) A

namespace OpenLevelDescent
variable {S : Scheme.{u}} [IsNoetherian S] {g N : ℕ} [NeZero N]
  (A : Abelian.Schemes.AbelianScheme g S) (C : S.OpenCover.{u}) [Category C.I₀] [C.LocallyDirected]
  (l : ∀ i, (A.pullback (C.f i)).FullLevel N)
  (hl : ∀ {i j : C.I₀} (f : i ⟶ j),
    ((l j).pullback (C.trans f)).transport
      (A.openCoverParameterIso C f).symm = l i)

private def chartPoint (i : C.I₀) :
    Directed.FamilyHomGluing.DirectedFamilyHomGluing.test C i ⟶ A.fullLevelParameter N :=
  (A.fullLevelParameterPointEquiv N _).symm (l i)

include hl in
private theorem chartPoint_natural {i j : C.I₀} (f : i ⟶ j) :
    Directed.FamilyHomGluing.DirectedFamilyHomGluing.testMap C f ≫ chartPoint A C l j = chartPoint A C l i := by
  apply (A.fullLevelParameterPointEquiv N _).injective
  have hn := A.fullLevelParameterPointEquiv_natural N
    (Directed.FamilyHomGluing.DirectedFamilyHomGluing.testMap C f) (chartPoint A C l j)
  rw [show A.fullLevelParameterPointEquiv N _ (chartPoint A C l j) = l j from
    Equiv.apply_symm_apply _ _] at hn
  exact hn.symm.trans ((hl f).trans (Equiv.apply_symm_apply _ _).symm)

include hl in
private theorem chartPoint_natural_left {i j : C.I₀} (f : i ⟶ j) :
    C.trans f ≫ (chartPoint A C l j).left = (chartPoint A C l i).left :=
  congrArg Over.Hom.left (chartPoint_natural A C l hl f)

private def basePoint : Over.mk (𝟙 S) ⟶ A.fullLevelParameter N :=
  Over.homMk
    (C.glueMorphismsOfLocallyDirected (fun i => (chartPoint A C l i).left)
      (chartPoint_natural_left A C l hl)) (by
        apply C.hom_ext
        intro i
        rw [← Category.assoc, C.map_glueMorphismsOfLocallyDirected,
          (chartPoint A C l i).w]
        exact (Category.comp_id (C.f i)).symm)

private abbrev chartToBase (i : C.I₀) : Directed.FamilyHomGluing.DirectedFamilyHomGluing.test C i ⟶ Over.mk (𝟙 S) :=
  Over.homMk (C.f i) (Category.comp_id _)

private theorem basePoint_on_chart (i : C.I₀) :
    chartToBase C i ≫ basePoint A C l hl = chartPoint A C l i := by
  apply Over.OverMorphism.ext
  exact C.map_glueMorphismsOfLocallyDirected (fun i => (chartPoint A C l i).left)
    (chartPoint_natural_left A C l hl) i

private def identityChartIso (i : C.I₀) :
    (A.pullback (C.f i)).scheme ≅ ((A.pullback (𝟙 S)).pullback (C.f i)).scheme :=
  A.parameterPullbackIso (chartToBase C i)

private instance identityChartIso_symm_group (i : C.I₀) :
    IsMonHom (identityChartIso A C i).symm.hom :=
  Abelian.Schemes.AbelianScheme.parameterPullbackIso_symm_isMonHom (chartToBase C i) A

private def identityLevel : (A.pullback (𝟙 S)).FullLevel N :=
  A.fullLevelParameterPointEquiv N (Over.mk (𝟙 S)) (basePoint A C l hl)

/-- The original full ordered level on the glued abelian scheme. -/
def _root_.OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme.level : A.FullLevel N :=
  (identityLevel A C l hl).transport A.pullbackIdIso

theorem _root_.OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme.level_pullback (i : C.I₀) : (Abelian.Schemes.AbelianScheme.level A C l hl).pullback (C.f i) = l i := by
  have hi : (Abelian.Schemes.AbelianScheme.level A C l hl).pullback (𝟙 S) = identityLevel A C l hl :=
    Abelian.Schemes.AbelianScheme.FullLevel.pullback_transportId (identityLevel A C l hl)
  have hcan := Abelian.Schemes.AbelianScheme.FullLevel.transport_parameterPullback A (chartToBase C i) (Abelian.Schemes.AbelianScheme.level A C l hl)
  have hrep := A.fullLevelParameterPointEquiv_natural N (chartToBase C i) (basePoint A C l hl)
  change (((Abelian.Schemes.AbelianScheme.level A C l hl).pullback (𝟙 S)).pullback (C.f i)).transport
      (identityChartIso A C i).symm =
        (Abelian.Schemes.AbelianScheme.level A C l hl).pullback (C.f i) at hcan
  rw [hi] at hcan
  change ((identityLevel A C l hl).pullback (C.f i)).transport
    (identityChartIso A C i).symm =
      A.fullLevelParameterPointEquiv N _ (chartToBase C i ≫ basePoint A C l hl) at hrep
  exact hcan.symm.trans (hrep.trans
    ((congrArg (A.fullLevelParameterPointEquiv N _)
      (basePoint_on_chart A C l hl i)).trans (Equiv.apply_symm_apply _ _)))

end OpenLevelDescent

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Level.OpenDescent.AbelianScheme

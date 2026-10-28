import OAI.AlgebraicGeometry.PELModuli.IntegralModel.ClosedTwistKernel
import OAI.AlgebraicGeometry.SheafCohomology.Projective.FrameSections
import Mathlib.Topology.Sheaves.SheafCondition.UniqueGluing

/-! # Global Twist Kernel -/

namespace OAI.AlgebraicGeometry.PELModuli.IntegralModel.GlobalTwistKernel

noncomputable section

/-! The global twisted structure-sheaf map has precisely the kernel detected
by the actual ideal sheaf in affine local frames. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open _root_.CategoryTheory _root_.AlgebraicGeometry MonoidalCategory Opposite

namespace PolarizationEmbedding

open OAI.AlgebraicGeometry.SheafCohomology.Projective.FrameSections
universe u
local instance c44GlobalTwistKernelMonoidal (X : Scheme.{u}) : MonoidalCategory X.Modules := SheafCohomology.Projective.Monoidal.Scheme.Modules.monoidalCategory X

theorem affineRestriction_map_app {X : Scheme.{u}} {M N : X.Modules} (q : M ⟶ N)
    (U : X.affineOpens) (x : Γ(M, ⊤)) :
    SheafCohomology.Projective.FrameSections.localTrivializationRestriction N U (q.app ⊤ x) =
      ((Scheme.Modules.restrictFunctor U.1.ι).map q).app ⊤
        (SheafCohomology.Projective.FrameSections.localTrivializationRestriction M U x) :=
  SheafCohomology.Projective.FrameSections.localTrivializationRestriction_map q U x

theorem affineAmbientSection_eq_topIso {X : Scheme.{u}} (U : X.affineOpens)
    (r : Γ(U.1.toScheme, ⊤)) : SheafCohomology.Projective.FrameSections.affineOpenAmbientSection U r = U.1.topIso.hom r := by
  have h := SheafCohomology.Projective.FrameSections.affineOpenTopSection_ambientSection U r
  rw [SheafCohomology.Projective.FrameSections.affineOpenTopSection_eq_topIso_inv] at h
  have h' := congrArg U.1.topIso.hom h
  simpa only [Iso.inv_hom_id_apply] using h'

theorem globalSection_zero_iff_affine_cover {X : Scheme.{u}} (M : X.Modules)
    {ι : Type*} (U : ι → X.affineOpens) (hU : (⊤ : X.Opens) ≤ ⨆ i, (U i).1)
    (x : Γ(M, ⊤)) : x = 0 ↔ ∀ i, SheafCohomology.Projective.FrameSections.localTrivializationRestriction M (U i) x = 0 := by
  constructor
  · rintro rfl i
    exact SheafCohomology.Projective.FrameSections.localTrivializationRestriction_zero M (U i)
  · intro h
    let F : TopCat.Sheaf AddCommGrpCat X := (SheafOfModules.toSheaf X.ringCatSheaf).obj M
    apply F.eq_of_locally_eq' (fun i => (U i).1) ⊤ (fun _ => homOfLE le_top) hU
    intro i
    change M.presheaf.map (U i).1.leTop.op x = M.presheaf.map (U i).1.leTop.op 0
    rw [map_zero]
    exact (SheafCohomology.Projective.FrameSections.localTrivializationRestriction_eq_zero_iff M (U i) x).mp (h i)

theorem globalTwistedStructureMap_zero_iff {X Y : Scheme.{u}} (f : X ⟶ Y) [QuasiCompact f]
    (L : Y.Modules) {ι : Type*} (U : ι → Y.affineOpens)
    (hU : (⊤ : Y.Opens) ≤ ⨆ i, (U i).1)
    (e : ∀ i, L.restrict (U i).1.ι ≅ SheafCohomology.Projective.Invertible.Scheme.Modules.unitObj (U i).1.toScheme)
    (x : Γ(L, ⊤)) :
    ((tensorRight L).map (SheafOfModules.unitToPushforwardObjUnit f.toRingCatSheafHom)).app ⊤
      ((Open.TwistKernel.PolarizationEmbedding.unitTensorLineIso L).inv.app ⊤ x) = 0 ↔
      ∀ i, SheafCohomology.Projective.FrameSections.localTrivializationCoefficient L (U i) (e i) x ∈ f.ker.ideal (U i) := by
  rw [globalSection_zero_iff_affine_cover _ U hU]
  apply forall_congr'
  intro i
  rw [affineRestriction_map_app
    ((tensorRight L).map (SheafOfModules.unitToPushforwardObjUnit f.toRingCatSheafHom))]
  erw [affineRestriction_map_app (Open.TwistKernel.PolarizationEmbedding.unitTensorLineIso L).inv]
  rw [ClosedTwistKernel.PolarizationEmbedding.twistedStructureMap_zero_iff_mem_ideal]
  rw [SheafCohomology.Projective.FrameSections.localTrivializationCoefficient, affineAmbientSection_eq_topIso]
  rfl

end PolarizationEmbedding

end

end OAI.AlgebraicGeometry.PELModuli.IntegralModel.GlobalTwistKernel

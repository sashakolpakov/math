import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.ReducedFrame
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Pullback.TensorFrame

/-! # Reduced Open Frame Converse -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.ReducedOpenFrameConverse

noncomputable section

section

/-! Tensor products of prescribed reduced frames normalize the
canonical tensor frame through the actual commuting open square. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry MonoidalCategory
open OAI.AlgebraicGeometry.Isogenies.NeighborCounting.FramedHom

local instance reducedTensorMonoidal (X : Scheme.{0}) : MonoidalCategory X.Modules :=
  SheafCohomology.Projective.Monoidal.Scheme.Modules.monoidalCategory X
local instance reducedTensorPullbackMonoidal {X Y : Scheme.{0}} (f : X ⟶ Y) :
    (Scheme.Modules.pullback f).Monoidal := SheafCohomology.Projective.PullbackTensorGeneral.Scheme.Modules.pullbackMonoidal f

variable {X Y : Scheme.{0}} (r : X ⟶ Y) (U : Y.Opens)

def reducedOpenSecondComparison :
    Scheme.Modules.pullback r ⋙ Scheme.Modules.pullback (r ⁻¹ᵁ U).ι ≅
      Scheme.Modules.pullback ((r ∣_ U) ≫ U.ι) :=
  Scheme.Modules.pullbackComp (r ⁻¹ᵁ U).ι r ≪≫
    (Scheme.Modules.pullbackCongr (morphismRestrict_ι r U)).symm

theorem reducedOpenSecondComparison_monoidal : (reducedOpenSecondComparison r U).hom.IsMonoidal := by
  let : (Scheme.Modules.pullbackComp (r ⁻¹ᵁ U).ι r).hom.IsMonoidal :=
    SheafCohomology.Projective.PullbackCompMonoidal.Scheme.Modules.pullbackComp_hom_isMonoidal (r ⁻¹ᵁ U).ι r
  let : (Scheme.Modules.pullbackCongr (morphismRestrict_ι r U)).inv.IsMonoidal :=
    SheafCohomology.Projective.PullbackFrameComposition.pullbackCongr_inv_isMonoidal (morphismRestrict_ι r U)
  change NatTrans.IsMonoidal ((Scheme.Modules.pullbackComp (r ⁻¹ᵁ U).ι r).hom ≫
    (Scheme.Modules.pullbackCongr (morphismRestrict_ι r U)).inv)
  exact NatTrans.IsMonoidal.comp _ _

theorem reducedOpenFrame_compared_iff {M : Y.Modules}
    (e₀ : (Scheme.Modules.pullback r).obj M ≅ ArithmeticGeometry.OrdinaryLocus.Openness.LineBundle.Construction.structureSheafModule X)
    (e : (Scheme.Modules.pullback U.ι).obj M ≅ ArithmeticGeometry.OrdinaryLocus.Openness.LineBundle.Construction.structureSheafModule U.toScheme) :
    Isogenies.NeighborCounting.FramedHom.pullbackFrame (r ∣_ U) e = ReducedFrame.reducedOpenFrame r e₀ U ↔
      Pullback.TensorFrame.comparedPullbackFrame U.ι (r ∣_ U) ((r ∣_ U) ≫ U.ι) (Scheme.Modules.pullbackComp (r ∣_ U) U.ι) e =
        Pullback.TensorFrame.comparedPullbackFrame r (r ⁻¹ᵁ U).ι ((r ∣_ U) ≫ U.ι) (reducedOpenSecondComparison r U) e₀ := by
  let A := (Scheme.Modules.pullbackComp (r ∣_ U) U.ι).app M
  let B := (Scheme.Modules.pullbackCongr (morphismRestrict_ι r U)).app M ≪≫
    (Scheme.Modules.pullbackComp (r ⁻¹ᵁ U).ι r).symm.app M ≪≫ Isogenies.NeighborCounting.FramedHom.pullbackFrame (r ⁻¹ᵁ U).ι e₀
  change Isogenies.NeighborCounting.FramedHom.pullbackFrame (r ∣_ U) e = A ≪≫ B ↔
    A.symm ≪≫ RepresentationTheory.Theta.Geometric.Pullback.FrameComposition.pullbackGlobalFrame (r ∣_ U) e =
      (Scheme.Modules.pullbackCongr (morphismRestrict_ι r U)).app M ≪≫
        (Scheme.Modules.pullbackComp (r ⁻¹ᵁ U).ι r).symm.app M ≪≫
          RepresentationTheory.Theta.Geometric.Pullback.FrameComposition.pullbackGlobalFrame (r ⁻¹ᵁ U).ι e₀
  rw [ReducedFrame.nativePullbackFrame_agrees, ReducedFrame.nativePullbackFrame_agrees]
  change Isogenies.NeighborCounting.FramedHom.pullbackFrame (r ∣_ U) e = A ≪≫ B ↔ A.symm ≪≫ Isogenies.NeighborCounting.FramedHom.pullbackFrame (r ∣_ U) e = B
  constructor
  · intro h
    exact (congrArg (fun q => A.symm ≪≫ q) h).trans (Iso.symm_self_id_assoc A B)
  · intro h
    exact (Iso.self_symm_id_assoc A (Isogenies.NeighborCounting.FramedHom.pullbackFrame (r ∣_ U) e)).symm.trans
      (congrArg (fun q => A ≪≫ q) h)

theorem reducedOpenFrame_tensor {M N : Y.Modules}
    (e₀ : (Scheme.Modules.pullback r).obj M ≅ ArithmeticGeometry.OrdinaryLocus.Openness.LineBundle.Construction.structureSheafModule X)
    (d₀ : (Scheme.Modules.pullback r).obj N ≅ ArithmeticGeometry.OrdinaryLocus.Openness.LineBundle.Construction.structureSheafModule X)
    (e : (Scheme.Modules.pullback U.ι).obj M ≅ ArithmeticGeometry.OrdinaryLocus.Openness.LineBundle.Construction.structureSheafModule U.toScheme)
    (d : (Scheme.Modules.pullback U.ι).obj N ≅ ArithmeticGeometry.OrdinaryLocus.Openness.LineBundle.Construction.structureSheafModule U.toScheme)
    (he : Isogenies.NeighborCounting.FramedHom.pullbackFrame (r ∣_ U) e = ReducedFrame.reducedOpenFrame r e₀ U)
    (hd : Isogenies.NeighborCounting.FramedHom.pullbackFrame (r ∣_ U) d = ReducedFrame.reducedOpenFrame r d₀ U) :
    Isogenies.NeighborCounting.FramedHom.pullbackFrame (r ∣_ U) (Pullback.TensorFrame.pullbackTensorFrame U.ι M N e d) =
      ReducedFrame.reducedOpenFrame r (Pullback.TensorFrame.pullbackTensorFrame r M N e₀ d₀) U := by
  let : (Scheme.Modules.pullbackComp (r ∣_ U) U.ι).hom.IsMonoidal :=
    SheafCohomology.Projective.PullbackCompMonoidal.Scheme.Modules.pullbackComp_hom_isMonoidal (r ∣_ U) U.ι
  let : (reducedOpenSecondComparison r U).hom.IsMonoidal := reducedOpenSecondComparison_monoidal r U
  apply (reducedOpenFrame_compared_iff r U _ _).mpr
  exact Pullback.TensorFrame.comparedTensorFrame_eq U.ι (r ∣_ U) r (r ⁻¹ᵁ U).ι ((r ∣_ U) ≫ U.ι)
    (Scheme.Modules.pullbackComp (r ∣_ U) U.ι) (reducedOpenSecondComparison r U) M N e d e₀ d₀
    ((reducedOpenFrame_compared_iff r U e₀ e).mp he)
    ((reducedOpenFrame_compared_iff r U d₀ d).mp hd)

end

/-! A local pullback frame whose chart pullback is the prescribed
global frame has exactly the required reduced local trivialization. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open OAI.AlgebraicGeometry.Isogenies.NeighborCounting.FramedHom

theorem pullbackChartFrame_compared {X Y : Scheme.{0}} (r : X ⟶ Y) (M : Y.Modules) (U : Y.Opens)
    (e : (Scheme.Modules.pullback U.ι).obj M ≅ ArithmeticGeometry.OrdinaryLocus.Openness.LineBundle.Construction.structureSheafModule U.toScheme) :
    RepresentationTheory.Theta.Geometric.OpenFramesFactored.pullbackChartFrame r M U e =
      (reducedOpenSecondComparison r U).app M ≪≫
        Pullback.TensorFrame.comparedPullbackFrame U.ι (r ∣_ U) ((r ∣_ U) ≫ U.ι) (Scheme.Modules.pullbackComp (r ∣_ U) U.ι) e := by
  let A := (Scheme.Modules.pullbackComp (r ⁻¹ᵁ U).ι r).app M
  let B := (Scheme.Modules.pullbackCongr (morphismRestrict_ι r U)).app M
  let C := (Scheme.Modules.pullbackComp (r ∣_ U) U.ι).app M
  let q := RepresentationTheory.Theta.Geometric.Pullback.FrameComposition.pullbackGlobalFrame (r ∣_ U) e
  change A ≪≫ (Scheme.Modules.pullbackCongr (morphismRestrict_ι r U).symm).app M ≪≫ C.symm ≪≫ q =
    (A ≪≫ B.symm) ≪≫ C.symm ≪≫ q
  exact (congrArg (fun b => A ≪≫ b ≪≫ C.symm ≪≫ q)
    (ReducedFrame.pullbackCongr_symm_app (morphismRestrict_ι r U) M)).trans
      (Iso.trans_assoc A B.symm (C.symm ≪≫ q)).symm

theorem reducedOpenFrame_of_chart {X Y : Scheme.{0}} (r : X ⟶ Y) {M : Y.Modules}
    (e₀ : (Scheme.Modules.pullback r).obj M ≅ ArithmeticGeometry.OrdinaryLocus.Openness.LineBundle.Construction.structureSheafModule X) (U : Y.Opens)
    (e : (Scheme.Modules.pullback U.ι).obj M ≅ ArithmeticGeometry.OrdinaryLocus.Openness.LineBundle.Construction.structureSheafModule U.toScheme)
    (h : RepresentationTheory.Theta.Geometric.OpenFramesFactored.pullbackChartFrame r M U e = Isogenies.NeighborCounting.FramedHom.pullbackFrame (r ⁻¹ᵁ U).ι e₀) :
    Isogenies.NeighborCounting.FramedHom.pullbackFrame (r ∣_ U) e = ReducedFrame.reducedOpenFrame r e₀ U := by
  apply (reducedOpenFrame_compared_iff r U e₀ e).mpr
  let B := (reducedOpenSecondComparison r U).app M
  have hh := congrArg (fun q => B.symm ≪≫ q)
    ((pullbackChartFrame_compared r M U e).symm.trans h)
  exact (Iso.symm_self_id_assoc B _).symm.trans
    (hh.trans (congrArg (fun q => B.symm ≪≫ q) (ReducedFrame.nativePullbackFrame_agrees (r ⁻¹ᵁ U).ι e₀).symm))

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.ReducedOpenFrameConverse

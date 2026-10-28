import OAI.RepresentationTheory.Theta.Geometric.OpenFramesFactored
import OAI.AlgebraicGeometry.Isogenies.NeighborCounting.FramedHom

/-! # Reduced Frame -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.ReducedFrame

noncomputable section

section

/-! The two proved native frame APIs use the same actual structure
sheaf pullback isomorphism. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

theorem nativePullbackUnit_agrees {X Y : Scheme.{0}} (f : X ⟶ Y) :
    SheafCohomology.Projective.Invertible.Scheme.Modules.pullbackUnitIso f = ArithmeticGeometry.OrdinaryLocus.Openness.LineBundle.Construction.pullbackStructureSheafIso f := by
  apply Iso.ext
  rfl

theorem nativePullbackFrame_agrees {X Y : Scheme.{0}} (f : X ⟶ Y) {M : Y.Modules}
    (e : M ≅ ArithmeticGeometry.OrdinaryLocus.Openness.LineBundle.Construction.structureSheafModule Y) :
    RepresentationTheory.Theta.Geometric.Pullback.FrameComposition.pullbackGlobalFrame f e = Isogenies.NeighborCounting.FramedHom.pullbackFrame f e := by
  unfold RepresentationTheory.Theta.Geometric.Pullback.FrameComposition.pullbackGlobalFrame Isogenies.NeighborCounting.FramedHom.pullbackFrame
  rw [nativePullbackUnit_agrees]
  rfl

theorem pullbackCongr_symm_app {X Y : Scheme.{0}} {f g : X ⟶ Y} (h : f = g) (M : Y.Modules) :
    (Scheme.Modules.pullbackCongr h.symm).app M = ((Scheme.Modules.pullbackCongr h).app M).symm := by
  cases h
  rfl

end

section

/-! A prescribed global frame after pullback determines the required
local reduced frame through the actual commuting open square. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open OAI.AlgebraicGeometry.Isogenies.NeighborCounting.FramedHom

variable {X Y : Scheme.{0}} (r : X ⟶ Y) {M : Y.Modules}
    (e₀ : (Scheme.Modules.pullback r).obj M ≅ ArithmeticGeometry.OrdinaryLocus.Openness.LineBundle.Construction.structureSheafModule X) (U : Y.Opens)

def reducedOpenFrame :
    (Scheme.Modules.pullback (r ∣_ U)).obj ((Scheme.Modules.pullback U.ι).obj M) ≅
      ArithmeticGeometry.OrdinaryLocus.Openness.LineBundle.Construction.structureSheafModule (r ⁻¹ᵁ U).toScheme :=
  (Scheme.Modules.pullbackComp (r ∣_ U) U.ι).app M ≪≫
    (Scheme.Modules.pullbackCongr (morphismRestrict_ι r U)).app M ≪≫
    (Scheme.Modules.pullbackComp (r ⁻¹ᵁ U).ι r).symm.app M ≪≫
    Isogenies.NeighborCounting.FramedHom.pullbackFrame (r ⁻¹ᵁ U).ι e₀

theorem reducedOpenFrame_chart (e : (Scheme.Modules.pullback U.ι).obj M ≅ ArithmeticGeometry.OrdinaryLocus.Openness.LineBundle.Construction.structureSheafModule U.toScheme)
    (he : Isogenies.NeighborCounting.FramedHom.pullbackFrame (r ∣_ U) e = reducedOpenFrame r e₀ U) :
    RepresentationTheory.Theta.Geometric.OpenFramesFactored.pullbackChartFrame r M U e = Isogenies.NeighborCounting.FramedHom.pullbackFrame (r ⁻¹ᵁ U).ι e₀ := by
  let A := (Scheme.Modules.pullbackComp (r ⁻¹ᵁ U).ι r).app M
  let B := (Scheme.Modules.pullbackCongr (morphismRestrict_ι r U)).app M
  let C := (Scheme.Modules.pullbackComp (r ∣_ U) U.ι).app M
  have hb : (Scheme.Modules.pullbackCongr (morphismRestrict_ι r U).symm).app M = B.symm :=
    pullbackCongr_symm_app (morphismRestrict_ι r U) M
  change Isogenies.NeighborCounting.FramedHom.pullbackFrame (r ∣_ U) e = C ≪≫ B ≪≫ A.symm ≪≫ Isogenies.NeighborCounting.FramedHom.pullbackFrame (r ⁻¹ᵁ U).ι e₀ at he
  simp only [RepresentationTheory.Theta.Geometric.OpenFramesFactored.pullbackChartFrame, RepresentationTheory.Theta.Geometric.FactoredPullbackFrames.factoredPullbackFrame, nativePullbackFrame_agrees]
  change A ≪≫ (Scheme.Modules.pullbackCongr (morphismRestrict_ι r U).symm).app M ≪≫ C.symm ≪≫
    Isogenies.NeighborCounting.FramedHom.pullbackFrame (r ∣_ U) e = _
  rw [hb, he]
  simp only [Iso.symm_self_id_assoc, Iso.self_symm_id_assoc]

end

/-! The prescribed reduced local frame is natural in actual module
isomorphisms, through the original pullback comparison isomorphisms. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open OAI.AlgebraicGeometry.Isogenies.NeighborCounting.FramedHom

theorem transportedFrame_precomp {C D : Type*} [Category C] [Category D]
    {F G : C ⥤ D} (η : F ≅ G) {M N : C} (q : N ≅ M) {K : D} (e : G.obj M ≅ K) :
    η.app N ≪≫ G.mapIso q ≪≫ e = F.mapIso q ≪≫ η.app M ≪≫ e := by
  apply Iso.ext
  exact (Category.assoc _ _ _).symm.trans
    ((congrArg (fun f => f ≫ e.hom) (η.hom.naturality q.hom).symm).trans (Category.assoc _ _ _))

theorem pullbackFrame_precomp {X Y : Scheme.{0}} (r : X ⟶ Y) {M N : Y.Modules}
    (q : N ≅ M) (e : M ≅ ArithmeticGeometry.OrdinaryLocus.Openness.LineBundle.Construction.structureSheafModule Y) :
    Isogenies.NeighborCounting.FramedHom.pullbackFrame r (q ≪≫ e) = (Scheme.Modules.pullback r).mapIso q ≪≫ Isogenies.NeighborCounting.FramedHom.pullbackFrame r e := by
  simp only [Isogenies.NeighborCounting.FramedHom.pullbackFrame, Functor.mapIso_trans, Iso.trans_assoc]

def reducedOpenFrameTransport {X Y : Scheme.{0}} (r : X ⟶ Y) (U : Y.Opens) :
    Scheme.Modules.pullback U.ι ⋙ Scheme.Modules.pullback (r ∣_ U) ≅
      Scheme.Modules.pullback r ⋙ Scheme.Modules.pullback (r ⁻¹ᵁ U).ι :=
  Scheme.Modules.pullbackComp (r ∣_ U) U.ι ≪≫
    Scheme.Modules.pullbackCongr (morphismRestrict_ι r U) ≪≫
    (Scheme.Modules.pullbackComp (r ⁻¹ᵁ U).ι r).symm

theorem reducedOpenFrame_precomp {X Y : Scheme.{0}} (r : X ⟶ Y) {M N : Y.Modules}
    (q : N ≅ M) (e₀ : (Scheme.Modules.pullback r).obj M ≅ ArithmeticGeometry.OrdinaryLocus.Openness.LineBundle.Construction.structureSheafModule X) (U : Y.Opens) :
    reducedOpenFrame r ((Scheme.Modules.pullback r).mapIso q ≪≫ e₀) U =
      (Scheme.Modules.pullback (r ∣_ U)).mapIso ((Scheme.Modules.pullback U.ι).mapIso q) ≪≫
        reducedOpenFrame r e₀ U := by
  change (reducedOpenFrameTransport r U).app N ≪≫
    Isogenies.NeighborCounting.FramedHom.pullbackFrame (r ⁻¹ᵁ U).ι ((Scheme.Modules.pullback r).mapIso q ≪≫ e₀) =
      (Scheme.Modules.pullback U.ι ⋙ Scheme.Modules.pullback (r ∣_ U)).mapIso q ≪≫
        (reducedOpenFrameTransport r U).app M ≪≫ Isogenies.NeighborCounting.FramedHom.pullbackFrame (r ⁻¹ᵁ U).ι e₀
  rw [pullbackFrame_precomp]
  exact transportedFrame_precomp (reducedOpenFrameTransport r U) q (Isogenies.NeighborCounting.FramedHom.pullbackFrame (r ⁻¹ᵁ U).ι e₀)

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.ReducedFrame

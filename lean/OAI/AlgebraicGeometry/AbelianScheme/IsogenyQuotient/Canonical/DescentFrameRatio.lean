import OAI.AlgebraicGeometry.Picard.Homomorphisms.CanonicalDescentFrames
import OAI.AlgebraicGeometry.Picard.PoincareBundle.GlobalPullbackFrame

/-! # Descent Frame Ratio -/

namespace OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Canonical.DescentFrameRatio.Construction

noncomputable section

/-! Canonical line descent computes the ratio of the two actual
pullback frames in their common fiber. This compares CartierDuality's scalar
convention directly with PoincareBundle's frame-ratio convention. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

open OAI.AlgebraicGeometry.Picard.Homomorphisms.CanonicalDescentFrames.Construction OAI.AlgebraicGeometry.Picard.PoincareBundle.Line.FrameUnits OAI.AlgebraicGeometry.Picard.PoincareBundle.GlobalPullbackFrame

universe u

theorem frame_conjugation_end {C : Type*} [Category* C] {U X Y Z : C}
    (e : X ≅ U) (d : Y ≅ U) (a : X ≅ Z) (b : Y ≅ Z) :
    (e.symm ≪≫ a).hom ≫ (d.symm ≪≫ b).inv = e.inv ≫ (a.hom ≫ b.inv) ≫ d.hom := by
  simp only [Iso.trans_hom, Iso.trans_inv, Iso.symm_hom, Iso.symm_inv, Category.assoc]

theorem atPoint_eq_native_frame {S : Scheme.{u}} {A B T : Over S}
    (f : A ⟶ B) (L : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle B.left)
    (s : AbelianModuli.HilbertConstruction.Line.Bundles.structureModule A.left ≅ (Scheme.Modules.pullback f.left).obj L.sheaf)
    (q : T ⟶ B) (x : T ⟶ A) (hx : x ≫ f = q) :
    Picard.PoincareBundle.GlobalPullbackFrame.atPoint f ⟨L.sheaf, L.locallyTrivial⟩ s x q hx =
      (Picard.Homomorphisms.FramedDescentScalars.Construction.pulledModuleFrame s.symm x.left).symm ≪≫
        (Scheme.Modules.pullbackComp x.left f.left ≪≫
          Scheme.Modules.pullbackCongr (congrArg Over.Hom.left hx)).app L.sheaf :=
  congrArg (fun a => Picard.PoincareBundle.FrameRatioPullback.pullFrame x.left s ≪≫ a)
    (Picard.PoincareBundle.GlobalPullbackFrame.comparison_eq f ⟨L.sheaf, L.locallyTrivial⟩ x q hx)

theorem canonicalDescentScalar_eq_frameRatio {S : Scheme.{u}} {A B T : Over S}
    (f : A ⟶ B) (L : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle B.left)
    (s : AbelianModuli.HilbertConstruction.Line.Bundles.structureModule A.left ≅ (Scheme.Modules.pullback f.left).obj L.sheaf)
    (q : T ⟶ B) (x y : T ⟶ A) (hx : x ≫ f = q) (hy : y ≫ f = q) :
    Picard.Homomorphisms.FramedDescentScalars.Construction.framedDescentScalar (Picard.Homomorphisms.CanonicalDescentFrames.Construction.canonicalModuleDescent f.left L.sheaf) s.symm q.left x.left y.left
      (congrArg Over.Hom.left hx) (congrArg Over.Hom.left hy) =
    (Picard.PoincareBundle.Line.FrameUnits.frameRatio (Picard.PoincareBundle.GlobalPullbackFrame.atPoint f ⟨L.sheaf, L.locallyTrivial⟩ s x q hx)
      (Picard.PoincareBundle.GlobalPullbackFrame.atPoint f ⟨L.sheaf, L.locallyTrivial⟩ s y q hy) : Γ(T.left, ⊤)) := by
  have hc := Picard.Homomorphisms.CanonicalDescentFrames.Construction.canonicalModuleDescent_hom f.left L.sheaf q.left x.left y.left
    (congrArg Over.Hom.left hx) (congrArg Over.Hom.left hy)
  have he := congrArg (fun a => (Picard.Homomorphisms.FramedDescentScalars.Construction.pulledModuleFrame s.symm x.left).inv ≫ a ≫
    (Picard.Homomorphisms.FramedDescentScalars.Construction.pulledModuleFrame s.symm y.left).hom) hc
  change AbelianModuli.HilbertConstruction.Frame.Coordinates.structureModuleEndValue T.left (Picard.Homomorphisms.FramedDescentScalars.Construction.framedDescentEnd (Picard.Homomorphisms.CanonicalDescentFrames.Construction.canonicalModuleDescent f.left L.sheaf) s.symm
    q.left x.left y.left (congrArg Over.Hom.left hx) (congrArg Over.Hom.left hy)) =
      AbelianModuli.HilbertConstruction.Frame.Coordinates.structureModuleEndValue T.left
        ((Picard.PoincareBundle.GlobalPullbackFrame.atPoint f ⟨L.sheaf, L.locallyTrivial⟩ s x q hx).hom ≫
          (Picard.PoincareBundle.GlobalPullbackFrame.atPoint f ⟨L.sheaf, L.locallyTrivial⟩ s y q hy).inv)
  apply congrArg (AbelianModuli.HilbertConstruction.Frame.Coordinates.structureModuleEndValue T.left)
  have hr := congrArg₂ (fun a b => a.hom ≫ b.inv)
    (atPoint_eq_native_frame f L s q x hx) (atPoint_eq_native_frame f L s q y hy)
  exact he.trans (hr.trans (frame_conjugation_end _ _ _ _)).symm

theorem canonicalDescentScalar_eq_one_of_frames {S : Scheme.{u}} {A B T : Over S}
    (f : A ⟶ B) (L : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle B.left)
    (s : AbelianModuli.HilbertConstruction.Line.Bundles.structureModule A.left ≅ (Scheme.Modules.pullback f.left).obj L.sheaf)
    (q : T ⟶ B) (x y : T ⟶ A) (hx : x ≫ f = q) (hy : y ≫ f = q)
    (hs : Picard.PoincareBundle.GlobalPullbackFrame.atPoint f ⟨L.sheaf, L.locallyTrivial⟩ s x q hx =
      Picard.PoincareBundle.GlobalPullbackFrame.atPoint f ⟨L.sheaf, L.locallyTrivial⟩ s y q hy) :
    Picard.Homomorphisms.FramedDescentScalars.Construction.framedDescentScalar (Picard.Homomorphisms.CanonicalDescentFrames.Construction.canonicalModuleDescent f.left L.sheaf) s.symm q.left x.left y.left
      (congrArg Over.Hom.left hx) (congrArg Over.Hom.left hy) = 1 :=
  (canonicalDescentScalar_eq_frameRatio f L s q x y hx hy).trans
    (congrArg Units.val ((Picard.PoincareBundle.Line.FrameUnits.frameRatio_eq_one_iff _ _).mpr hs))

end

end OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Canonical.DescentFrameRatio.Construction

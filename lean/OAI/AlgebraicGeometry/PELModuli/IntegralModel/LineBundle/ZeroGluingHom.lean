import OAI.AlgebraicGeometry.PELModuli.IntegralModel.LineBundle.ZeroGluing

/-! # Zero Gluing Hom -/

namespace OAI.AlgebraicGeometry.PELModuli.IntegralModel.LineBundle.ZeroGluingHom

noncomputable section

/-! The frame-preserving zero gluing has a native module-morphism
equation, with all isomorphism projections simplified before specialization. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

theorem iso_frame_hom {C : Type*} [Category* C] {A B V : C}
    (e : A ≅ B) (s : A ≅ V) (t : B ≅ V) (h : e ≪≫ t = s) :
    e.hom ≫ t.hom = s.hom := congrArg CategoryTheory.Iso.hom h

theorem lineBundleZeroGluing_preserves_frame_hom {X Y A B : Scheme.{0}} (L : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle X)
    (z : A ⟶ X) (frame : (L.pullback z).sheaf ≅ AbelianModuli.HilbertConstruction.Line.Bundles.structureModule A)
    (f g : Y ⟶ X) (w : B ⟶ Y) (a c : B ⟶ A)
    (hf : w ≫ f = a ≫ z) (hg : w ≫ g = c ≫ z)
    (e : (L.pullback f).sheaf ≅ (L.pullback g).sheaf)
    (he : (Scheme.Modules.pullback w).mapIso e ≪≫ SquareFrame.lineBundleSquareFrame L z frame g w c hg =
      SquareFrame.lineBundleSquareFrame L z frame f w a hf) :
    (SquareIsoFrames.lineBundleSquareTransportIso L f g z w a c hf.symm hg.symm e).hom ≫
        ((Scheme.Modules.pullback c).mapIso frame ≪≫ AbelianModuli.HilbertConstruction.Line.Bundles.structureModulePullbackIso c).hom =
      ((Scheme.Modules.pullback a).mapIso frame ≪≫ AbelianModuli.HilbertConstruction.Line.Bundles.structureModulePullbackIso a).hom :=
  congrArg CategoryTheory.Iso.hom (ZeroGluing.lineBundleZeroGluing_preserves_frame L z frame f g w a c hf hg e he)

end

end OAI.AlgebraicGeometry.PELModuli.IntegralModel.LineBundle.ZeroGluingHom

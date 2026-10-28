import OAI.AlgebraicGeometry.Picard.PoincareBundle.Line.FrameUnits

/-! # Frame Ratio Pullback -/

namespace OAI.AlgebraicGeometry.Picard.PoincareBundle.FrameRatioPullback

noncomputable section

/-!
# Naturality of the unit-valued frame obstruction under arbitrary scheme pullback
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

/-- Naturality of adjunction identifies the adjoint of a conjugated endomorphism. -/
theorem conjugate_homEquiv {C D : Type*} [Category C] [Category D]
    {L : C ⥤ D} {R : D ⥤ C} (a : L ⊣ R) {U : C} {V : D}
    (e : L.obj U ≅ V) (k : U ⟶ U) :
    a.homEquiv U V e.hom ≫ R.map (e.inv ≫ L.map k ≫ e.hom) =
      k ≫ a.homEquiv U V e.hom := by
  rw [← Adjunction.homEquiv_naturality_right, Iso.hom_inv_id_assoc,
    Adjunction.homEquiv_naturality_left]

open OAI.AlgebraicGeometry.Picard.PoincareBundle.Line.FrameUnits OAI.AlgebraicGeometry.Picard.PoincareBundle.Tensor.UnitPullback

variable {X Y : Scheme.{u}} (f : X ⟶ Y)

/-- Pullback of a structure-sheaf endomorphism, with its actual canonical unit identifications. -/
def pullEnd (a : AbelianModuli.HilbertConstruction.Line.Bundles.structureModule Y ⟶ AbelianModuli.HilbertConstruction.Line.Bundles.structureModule Y) : AbelianModuli.HilbertConstruction.Line.Bundles.structureModule X ⟶ AbelianModuli.HilbertConstruction.Line.Bundles.structureModule X :=
  (AbelianModuli.HilbertConstruction.Line.Bundles.structureModulePullbackIso f).inv ≫ (Scheme.Modules.pullback f).map a ≫
    (AbelianModuli.HilbertConstruction.Line.Bundles.structureModulePullbackIso f).hom

/-- The pulled-back endomorphism intertwines the actual map of structure sheaves. -/
theorem pullEnd_base (a : AbelianModuli.HilbertConstruction.Line.Bundles.structureModule Y ⟶ AbelianModuli.HilbertConstruction.Line.Bundles.structureModule Y) :
    Tensor.UnitPullback.baseUnitMap f ≫ (Scheme.Modules.pushforward f).map (pullEnd f a) = a ≫ Tensor.UnitPullback.baseUnitMap f := by
  have h := conjugate_homEquiv (Scheme.Modules.pullbackPushforwardAdjunction f)
    (AbelianModuli.HilbertConstruction.Line.Bundles.structureModulePullbackIso f) a
  rw [Tensor.UnitPullback.unitIso_homEquiv] at h
  exact h

/-- The scalar of the pullback is the pullback of the actual global function. -/
theorem scalar_pullEnd (a : AbelianModuli.HilbertConstruction.Line.Bundles.structureModule Y ⟶ AbelianModuli.HilbertConstruction.Line.Bundles.structureModule Y) :
    Line.FrameUnits.scalar (pullEnd f a) = f.appTop (Line.FrameUnits.scalar a) := by
  have h := congrArg
    (fun b : AbelianModuli.HilbertConstruction.Line.Bundles.structureModule Y ⟶ (Scheme.Modules.pushforward f).obj (AbelianModuli.HilbertConstruction.Line.Bundles.structureModule X) =>
      b.app ⊤ (1 : Γ(Y, ⊤))) (pullEnd_base f a)
  change (pullEnd f a).app ⊤ (f.appTop (1 : Γ(Y, ⊤))) = f.appTop (Line.FrameUnits.scalar a) at h
  rw [map_one] at h
  exact h

/-- Pullback of a line frame uses the canonical structure-sheaf isomorphism. -/
def pullFrame {M : Y.Modules} (s : AbelianModuli.HilbertConstruction.Line.Bundles.structureModule Y ≅ M) :
    AbelianModuli.HilbertConstruction.Line.Bundles.structureModule X ≅ (Scheme.Modules.pullback f).obj M :=
  (AbelianModuli.HilbertConstruction.Line.Bundles.structureModulePullbackIso f).symm ≪≫ (Scheme.Modules.pullback f).mapIso s

/-- The actual ratio is unchanged by applying one common isomorphism to both frames. -/
theorem frameRatio_postcomp {Z : Scheme.{u}} {M N : Z.Modules}
    (s t : AbelianModuli.HilbertConstruction.Line.Bundles.structureModule Z ≅ M) (e : M ≅ N) :
    Line.FrameUnits.frameRatio (s ≪≫ e) (t ≪≫ e) = Line.FrameUnits.frameRatio s t := by
  apply Units.ext
  change Line.FrameUnits.scalar ((s.hom ≫ e.hom) ≫ e.inv ≫ t.inv) = Line.FrameUnits.scalar (s.hom ≫ t.inv)
  simp only [Category.assoc, e.hom_inv_id_assoc]

/-- Frame ratios pull back by the genuine ring map on global sections. -/
theorem frameRatio_pullFrame {M : Y.Modules} (s t : AbelianModuli.HilbertConstruction.Line.Bundles.structureModule Y ≅ M) :
    Line.FrameUnits.frameRatio (pullFrame f s) (pullFrame f t) = Units.map f.appTop.hom (Line.FrameUnits.frameRatio s t) := by
  apply Units.ext
  change Line.FrameUnits.scalar
    (((AbelianModuli.HilbertConstruction.Line.Bundles.structureModulePullbackIso f).inv ≫ (Scheme.Modules.pullback f).map s.hom) ≫
      (Scheme.Modules.pullback f).map t.inv ≫ (AbelianModuli.HilbertConstruction.Line.Bundles.structureModulePullbackIso f).hom) =
    f.appTop (Line.FrameUnits.scalar (s.hom ≫ t.inv))
  rw [Category.assoc, ← (Scheme.Modules.pullback f).map_comp_assoc]
  exact scalar_pullEnd f (s.hom ≫ t.inv)

end

end OAI.AlgebraicGeometry.Picard.PoincareBundle.FrameRatioPullback

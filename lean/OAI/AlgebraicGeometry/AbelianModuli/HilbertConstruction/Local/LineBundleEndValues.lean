import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Local.LineBundleEndTransfer

/-! # Line Bundle End Values -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Local.LineBundleEndValues

noncomputable section

/-! Ambient values of scalar transfers agree on open refinements. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

variable {X Y Z : Scheme.{u}} {M : Y.Modules}

def localLineEndValue (f : X ⟶ Y) [IsOpenImmersion f] (φ : End M)
    (e : Line.Bundles.structureModule X ≅ (Scheme.Modules.pullback f).obj M)
    (U : Y.Opens) (hU : U ≤ f.opensRange) : Γ(Y, U) →ₗ[Γ(Y, U)] Γ(Y, U) :=
  OpenPullback.ModuleValues.openPullbackModuleValue f (LineBundleEndTransfer.localLineEndTransfer f φ e) U hU

theorem localLineEndValue_congr {f f' : X ⟶ Y} [IsOpenImmersion f] [IsOpenImmersion f']
    (h : f = f') (φ : End M)
    (e : Line.Bundles.structureModule X ≅ (Scheme.Modules.pullback f).obj M)
    (e' : Line.Bundles.structureModule X ≅ (Scheme.Modules.pullback f').obj M)
    (U : Y.Opens) (hU : U ≤ f.opensRange) (hU' : U ≤ f'.opensRange) :
    localLineEndValue f φ e U hU = localLineEndValue f' φ e' U hU' := by
  subst f'
  unfold localLineEndValue
  rw [LineBundleEndTransfer.localLineEndTransfer_independent f φ e e']

theorem localLineEndValue_comp (f : X ⟶ Y) (g : Y ⟶ Z)
    [IsOpenImmersion f] [IsOpenImmersion g] {P : Z.Modules} (φ : End P)
    (e : Line.Bundles.structureModule Y ≅ (Scheme.Modules.pullback g).obj P)
    (U : Z.Opens) (hU : U ≤ (f ≫ g).opensRange) :
    localLineEndValue (f ≫ g) φ (TensorPowerValues.refinedPullbackFrame f g e) U hU =
      localLineEndValue g φ e U (hU.trans (by
        rw [Scheme.Hom.opensRange_comp]
        exact g.image_le_opensRange f.opensRange)) := by
  unfold localLineEndValue
  rw [← LineBundleEndTransfer.localLineEndTransfer_comp]
  exact OpenPullback.RefinementNaturality.openPullbackModuleValue_comp f g _ U hU

theorem localLineEndValue_restriction (f : X ⟶ Y) [IsOpenImmersion f] (φ : End M)
    (e : Line.Bundles.structureModule X ≅ (Scheme.Modules.pullback f).obj M)
    (U : Y.Opens) (hU : U ≤ f.opensRange) :
    OpenModule.MapValues.openModuleMapValue f (OpenPullback.ModuleValues.pullbackModuleRestrictionMap f (LineBundleEndTransfer.localLineEndTransfer f φ e)) U hU =
      localLineEndValue f φ e U hU :=
  OpenPullback.ModuleValues.openPullbackModuleValue_restriction f (LineBundleEndTransfer.localLineEndTransfer f φ e) U hU

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Local.LineBundleEndValues

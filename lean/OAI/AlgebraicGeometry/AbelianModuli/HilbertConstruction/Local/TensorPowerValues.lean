import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Local.TensorPowerComposition
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.OpenPullback.RefinementNaturality

/-! # Tensor Power Values -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Local.TensorPowerValues

noncomputable section

/-! Frame-independent ambient values of local tensor-power comparisons, stable under refinement. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

variable {X Y Z : Scheme.{u}} {L M : Y.Modules}

def localTensorPowerValue (f : X ⟶ Y) [IsOpenImmersion f]
    (e : Line.Bundles.structureModule X ≅ (Scheme.Modules.pullback f).obj L)
    (t : Line.Bundles.structureModule X ≅ (Scheme.Modules.pullback f).obj M)
    (n : ℕ) (U : Y.Opens) (hU : U ≤ f.opensRange) :
    Γ(TensorPower.PowerSheaf.tensorPowerModule (Tensor.ProductSheaf.tensorModule L M) n, U) →ₗ[Γ(Y, U)]
      Γ(Tensor.ProductSheaf.tensorModule (TensorPower.PowerSheaf.tensorPowerModule L n) (TensorPower.PowerSheaf.tensorPowerModule M n), U) :=
  OpenPullback.ModuleValues.openPullbackModuleValue f (TensorPowerComparison.localTensorPowerComparisonIso f e.hom t.hom n).hom U hU

theorem localTensorPowerValue_independent (f : X ⟶ Y) [IsOpenImmersion f]
    (e e' : Line.Bundles.structureModule X ≅ (Scheme.Modules.pullback f).obj L)
    (t t' : Line.Bundles.structureModule X ≅ (Scheme.Modules.pullback f).obj M)
    (n : ℕ) (U : Y.Opens) (hU : U ≤ f.opensRange) :
    localTensorPowerValue f e t n U hU = localTensorPowerValue f e' t' n U hU := by
  unfold localTensorPowerValue
  rw [TensorPowerComparison.localTensorPowerComparisonIso_independent f e.hom e'.hom t.hom t'.hom n]

theorem localTensorPowerValue_congr {f f' : X ⟶ Y} [IsOpenImmersion f] [IsOpenImmersion f']
    (h : f = f')
    (e : Line.Bundles.structureModule X ≅ (Scheme.Modules.pullback f).obj L)
    (e' : Line.Bundles.structureModule X ≅ (Scheme.Modules.pullback f').obj L)
    (t : Line.Bundles.structureModule X ≅ (Scheme.Modules.pullback f).obj M)
    (t' : Line.Bundles.structureModule X ≅ (Scheme.Modules.pullback f').obj M)
    (n : ℕ) (U : Y.Opens) (hU : U ≤ f.opensRange) (hU' : U ≤ f'.opensRange) :
    localTensorPowerValue f e t n U hU = localTensorPowerValue f' e' t' n U hU' := by
  subst f'
  exact localTensorPowerValue_independent f e e' t t' n U hU

def refinedPullbackFrame (f : X ⟶ Y) (g : Y ⟶ Z) {P : Z.Modules}
    (e : Line.Bundles.structureModule Y ≅ (Scheme.Modules.pullback g).obj P) :
    Line.Bundles.structureModule X ≅ (Scheme.Modules.pullback (f ≫ g)).obj P :=
  ((Line.Bundles.structureModulePullbackIso f).symm ≪≫ (Scheme.Modules.pullback f).mapIso e) ≪≫
    (Scheme.Modules.pullbackComp f g).app P

theorem refine_localTensorPowerComparison
    (f : X ⟶ Y) (g : Y ⟶ Z) [IsOpenImmersion f] [IsOpenImmersion g] {P Q : Z.Modules}
    (e : Line.Bundles.structureModule Y ≅ (Scheme.Modules.pullback g).obj P)
    (t : Line.Bundles.structureModule Y ≅ (Scheme.Modules.pullback g).obj Q) (n : ℕ) :
    OpenPullback.Refinement.refineOpenPullbackMap f g (TensorPowerComparison.localTensorPowerComparisonIso g e.hom t.hom n).hom =
      (TensorPowerComparison.localTensorPowerComparisonIso (f ≫ g) (refinedPullbackFrame f g e).hom
        (refinedPullbackFrame f g t).hom n).hom := by
  apply (cancel_epi ((Scheme.Modules.pullbackComp f g).app
    (TensorPower.PowerSheaf.tensorPowerModule (Tensor.ProductSheaf.tensorModule P Q) n)).hom).mp
  change _ ≫ ((Scheme.Modules.pullbackComp f g).inv.app _ ≫ _ ≫ _) = _
  exact (((Scheme.Modules.pullbackComp f g).app
    (TensorPower.PowerSheaf.tensorPowerModule (Tensor.ProductSheaf.tensorModule P Q) n)).hom_inv_id_assoc _).trans
      (TensorPowerComposition.localTensorPowerComparisonIso_comp f g e.hom t.hom n)

theorem localTensorPowerValue_comp
    (f : X ⟶ Y) (g : Y ⟶ Z) [IsOpenImmersion f] [IsOpenImmersion g] {P Q : Z.Modules}
    (e : Line.Bundles.structureModule Y ≅ (Scheme.Modules.pullback g).obj P)
    (t : Line.Bundles.structureModule Y ≅ (Scheme.Modules.pullback g).obj Q)
    (n : ℕ) (U : Z.Opens) (hU : U ≤ (f ≫ g).opensRange) :
    localTensorPowerValue (f ≫ g) (refinedPullbackFrame f g e) (refinedPullbackFrame f g t) n U hU =
      localTensorPowerValue g e t n U (hU.trans (by
        rw [Scheme.Hom.opensRange_comp]
        exact g.image_le_opensRange f.opensRange)) := by
  unfold localTensorPowerValue
  rw [← refine_localTensorPowerComparison]
  exact OpenPullback.RefinementNaturality.openPullbackModuleValue_comp f g _ U hU

theorem localTensorPowerValue_restriction (f : X ⟶ Y) [IsOpenImmersion f]
    (e : Line.Bundles.structureModule X ≅ (Scheme.Modules.pullback f).obj L)
    (t : Line.Bundles.structureModule X ≅ (Scheme.Modules.pullback f).obj M)
    (n : ℕ) (U : Y.Opens) (hU : U ≤ f.opensRange) :
    OpenModule.MapValues.openModuleMapValue f (TensorPowerComparison.localTensorPowerRestrictionIso f e.hom t.hom n).hom U hU =
      localTensorPowerValue f e t n U hU :=
  OpenPullback.ModuleValues.openPullbackModuleValue_restriction f (TensorPowerComparison.localTensorPowerComparisonIso f e.hom t.hom n).hom U hU

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Local.TensorPowerValues

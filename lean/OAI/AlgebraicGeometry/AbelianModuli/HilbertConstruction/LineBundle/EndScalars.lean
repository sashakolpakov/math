import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Scalar.BaseChange

/-! # End Scalars -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.LineBundle.EndScalars

noncomputable section

/-! Scalar descriptions of line-bundle endomorphisms are independent of a chosen frame. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

variable {X Y : Scheme.{u}}

theorem structureModuleEnd_comp_comm (a b : End (Line.Bundles.structureModule X)) : a ≫ b = b ≫ a := by
  apply Global.Sections.structureModuleEndValue_injective X
  change Frame.Coordinates.structureModuleEndValue X (b * a) = Frame.Coordinates.structureModuleEndValue X (a * b)
  rw [map_mul, map_mul, mul_comm]

def framedEndScalar {M : X.Modules} (e : Line.Bundles.structureModule X ≅ M) (φ : End M) :
    End (Line.Bundles.structureModule X) := e.hom ≫ φ ≫ e.inv

theorem framedEndScalar_independent {M : X.Modules} (e f : Line.Bundles.structureModule X ≅ M) (φ : End M) :
    framedEndScalar e φ = framedEndScalar f φ := by
  have h := congrArg (fun a : End (Line.Bundles.structureModule X) => a ≫ f.hom ≫ e.inv)
    (structureModuleEnd_comp_comm (e.hom ≫ f.inv) (framedEndScalar f φ))
  simpa only [framedEndScalar, Category.assoc, Iso.inv_hom_id_assoc, Iso.hom_inv_id,
    Category.comp_id] using h

theorem framedEndScalar_injective {M : X.Modules} (e : Line.Bundles.structureModule X ≅ M) :
    Function.Injective (framedEndScalar e) := by
  intro φ ψ h
  exact (cancel_epi e.hom).mp
    ((cancel_mono e.inv).mp (by simpa only [framedEndScalar, Category.assoc] using h))

def pulledBackFrame (f : X ⟶ Y) {M : Y.Modules} (e : Line.Bundles.structureModule Y ≅ M) :
    Line.Bundles.structureModule X ≅ (Scheme.Modules.pullback f).obj M :=
  (Line.Bundles.structureModulePullbackIso f).symm ≪≫ (Scheme.Modules.pullback f).mapIso e

theorem framedEndScalar_pullback (f : X ⟶ Y) {M : Y.Modules}
    (e : Line.Bundles.structureModule Y ≅ M) (φ : End M) :
    framedEndScalar (pulledBackFrame f e) ((Scheme.Modules.pullback f).map φ) =
      (Line.Bundles.structureModulePullbackIso f).inv ≫
        (Scheme.Modules.pullback f).map (framedEndScalar e φ) ≫
          (Line.Bundles.structureModulePullbackIso f).hom := by
  simp only [framedEndScalar, pulledBackFrame, Iso.trans_hom, Iso.trans_inv, Iso.symm_hom,
    Iso.symm_inv, Functor.mapIso_hom, Functor.mapIso_inv, Functor.map_comp, Category.assoc]

theorem framedEndScalarValue_pullback (f : X ⟶ Y) {M : Y.Modules}
    (e : Line.Bundles.structureModule Y ≅ M) (φ : End M) :
    Frame.Coordinates.structureModuleEndValue X (framedEndScalar (pulledBackFrame f e)
      ((Scheme.Modules.pullback f).map φ)) =
        f.appTop (Frame.Coordinates.structureModuleEndValue Y (framedEndScalar e φ)) := by
  rw [framedEndScalar_pullback, Scalar.BaseChange.structureModuleEndValue_baseChange]

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.LineBundle.EndScalars

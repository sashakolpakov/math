import OAI.AlgebraicGeometry.Picard.PoincareBundle.Tensor.LinePullback

/-! # Line Bundles -/

namespace OAI.AlgebraicGeometry.Picard.PoincareBundle.Tensor.LineBundles

noncomputable section

/-!
# Actual tensor products of PoincareBundle line bundles and their arbitrary pullbacks
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

open OAI.AlgebraicGeometry.Picard.PoincareBundle.Line.Bundles

/-- The tensor product of two actual locally free rank-one sheaves is again locally free of rank one. -/
theorem tensor_isLine {X : Scheme.{u}} {M N : X.Modules} (hM : Line.Bundles.IsLine M) (hN : Line.Bundles.IsLine N) :
    Line.Bundles.IsLine (AbelianModuli.HilbertConstruction.Tensor.ProductSheaf.tensorModule M N) := by
  intro x
  obtain ⟨U, hxU, ⟨eM⟩⟩ := hM x
  obtain ⟨V, hxV, ⟨eN⟩⟩ := hN x
  refine ⟨U ⊓ V, ⟨hxU, hxV⟩, ⟨?_⟩⟩
  exact LinePullback.pullbackIso (U ⊓ V).ι M N hM hN ≪≫
    UnitPullback.tensorIso
      (LinePullback.frameRestrict M inf_le_left eM)
      (LinePullback.frameRestrict N inf_le_right eN) ≪≫
    AbelianModuli.HilbertConstruction.Tensor.ProductSheaf.tensorModuleUnitLeftIso (AbelianModuli.HilbertConstruction.Line.Bundles.structureModule (U ⊓ V).toScheme)

/-- Tensor product in the actual category of PoincareBundle line bundles. -/
def tensor {X : Scheme.{u}} (L M : Line.Bundles.LineBundle X) : Line.Bundles.LineBundle X :=
  ⟨AbelianModuli.HilbertConstruction.Tensor.ProductSheaf.tensorModule L.sheaf M.sheaf, tensor_isLine L.isLine M.isLine⟩

/-- The canonical tensor pullback isomorphism applies to arbitrary scheme morphisms. -/
def tensorPullbackIso {X Y : Scheme.{u}} (f : X ⟶ Y) (L M : Line.Bundles.LineBundle Y) :
    ((tensor L M).pullback f).sheaf ≅ (tensor (L.pullback f) (M.pullback f)).sheaf :=
  LinePullback.pullbackIso f L.sheaf M.sheaf L.isLine M.isLine

/-- Tensor product is independent of the chosen representatives of actual line-bundle classes. -/
def tensorClass {X : Scheme.{u}} (q r : Line.Bundles.LineBundleClass X) : Line.Bundles.LineBundleClass X :=
  Quotient.liftOn₂ q r (fun L M => Line.Bundles.LineBundleClass.mk (tensor L M)) (by
    intro L L' M M' ⟨a⟩ ⟨b⟩
    exact Quotient.sound ⟨UnitPullback.tensorIso a b⟩)

/-- The actual tensor classes commute. -/
theorem tensorClass_comm {X : Scheme.{u}} (q r : Line.Bundles.LineBundleClass X) : tensorClass q r = tensorClass r q := by
  induction q using Quotient.inductionOn with
  | _ L =>
    induction r using Quotient.inductionOn with
    | _ M => exact Quotient.sound ⟨AbelianModuli.HilbertConstruction.Tensor.ProductSheaf.tensorModuleCommIso L.sheaf M.sheaf⟩

/-- Pullback of tensor classes is tensor product of pullbacks, including inseparable morphisms. -/
theorem tensorClass_pullback {X Y : Scheme.{u}} (f : X ⟶ Y) (q r : Line.Bundles.LineBundleClass Y) :
    Line.Bundles.LineBundleClass.pullback f (tensorClass q r) =
      tensorClass (Line.Bundles.LineBundleClass.pullback f q) (Line.Bundles.LineBundleClass.pullback f r) := by
  induction q using Quotient.inductionOn with
  | _ L =>
    induction r using Quotient.inductionOn with
    | _ M => exact Quotient.sound ⟨tensorPullbackIso f L M⟩

end

end OAI.AlgebraicGeometry.Picard.PoincareBundle.Tensor.LineBundles

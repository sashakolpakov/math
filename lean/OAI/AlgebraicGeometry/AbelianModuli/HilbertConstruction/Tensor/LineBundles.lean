import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Tensor.ProductBaseChange

/-! # Line Bundles -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction

noncomputable section

/-! Tensor products of actual algebraic line bundles. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

variable {X Y : Scheme.{u}}

/-- A trivialization remains a trivialization on every smaller open subscheme. -/
def Line.Bundles.LineBundle.frameRestrict (L : Line.Bundles.LineBundle X) {U V : X.Opens} (h : U ≤ V)
    (e : (Scheme.Modules.pullback V.ι).obj L.sheaf ≅ Line.Bundles.structureModule V.toScheme) :
    (Scheme.Modules.pullback U.ι).obj L.sheaf ≅ Line.Bundles.structureModule U.toScheme :=
  (Scheme.Modules.pullbackCongr (X.homOfLE_ι h).symm).app L.sheaf ≪≫
    (Scheme.Modules.pullbackComp (X.homOfLE h) V.ι).symm.app L.sheaf ≪≫
      (Scheme.Modules.pullback (X.homOfLE h)).mapIso e ≪≫ Line.Bundles.structureModulePullbackIso (X.homOfLE h)

/-- The tensor product of locally free rank-one sheaves is again a line bundle. -/
def Line.Bundles.LineBundle.tensor (L M : Line.Bundles.LineBundle X) : Line.Bundles.LineBundle X where
  sheaf := Tensor.ProductSheaf.tensorModule L.sheaf M.sheaf
  locallyTrivial x := by
    obtain ⟨U, hxU, ⟨e⟩⟩ := L.locallyTrivial x
    obtain ⟨V, hxV, ⟨f⟩⟩ := M.locallyTrivial x
    refine ⟨U ⊓ V, ⟨hxU, hxV⟩, ⟨?_⟩⟩
    exact Tensor.ProductBaseChange.tensorModulePullbackIso (U ⊓ V).ι L.sheaf M.sheaf ≪≫
      Tensor.ProductSheaf.tensorModuleCongr (L.frameRestrict inf_le_left e) (M.frameRestrict inf_le_right f) ≪≫
        Tensor.ProductSheaf.tensorModuleUnitLeftIso (Line.Bundles.structureModule (U ⊓ V).toScheme)

/-- Tensor product of line-bundle classes is independent of the representatives. -/
def Line.Bundles.LineBundle.tensorClass (q r : Line.Bundles.LineBundle.IsoClass X) : Line.Bundles.LineBundle.IsoClass X :=
  Quotient.liftOn₂ q r (fun L M => Line.Bundles.LineBundle.classOf (L.tensor M)) (by
    intro L L' M M' ⟨e⟩ ⟨f⟩
    exact Quotient.sound ⟨Tensor.ProductSheaf.tensorModuleCongr e f⟩)

theorem Line.Bundles.LineBundle.tensorClass_comm (q r : Line.Bundles.LineBundle.IsoClass X) : Line.Bundles.LineBundle.tensorClass q r = Line.Bundles.LineBundle.tensorClass r q := by
  induction q using Quotient.inductionOn with
  | h L =>
    induction r using Quotient.inductionOn with
    | h M => exact Quotient.sound ⟨Tensor.ProductSheaf.tensorModuleCommIso L.sheaf M.sheaf⟩

@[simp]
theorem Line.Bundles.LineBundle.tensorClass_trivial_left (q : Line.Bundles.LineBundle.IsoClass X) : Line.Bundles.LineBundle.tensorClass (Line.Bundles.LineBundle.trivialClass X) q = q := by
  induction q using Quotient.inductionOn with
  | h L => exact Quotient.sound ⟨Tensor.ProductSheaf.tensorModuleUnitLeftIso L.sheaf⟩

@[simp]
theorem Line.Bundles.LineBundle.tensorClass_trivial_right (q : Line.Bundles.LineBundle.IsoClass X) : Line.Bundles.LineBundle.tensorClass q (Line.Bundles.LineBundle.trivialClass X) = q :=
  (Line.Bundles.LineBundle.tensorClass_comm _ _).trans (Line.Bundles.LineBundle.tensorClass_trivial_left q)

/-- Restriction of tensor products is tensor product of restrictions. -/
def Line.Bundles.LineBundle.tensorPullbackIso (f : X ⟶ Y) [IsOpenImmersion f] (L M : Line.Bundles.LineBundle Y) :
    ((L.tensor M).pullback f).sheaf ≅ ((L.pullback f).tensor (M.pullback f)).sheaf :=
  Tensor.ProductBaseChange.tensorModulePullbackIso f L.sheaf M.sheaf

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction

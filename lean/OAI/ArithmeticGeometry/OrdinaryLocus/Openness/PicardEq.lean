import OAI.ArithmeticGeometry.OrdinaryLocus.Openness.LineBundleAssociator

/-! # Picard Eq -/

namespace OAI.ArithmeticGeometry.OrdinaryLocus.Openness.PicardEq.Construction

noncomputable section

/-! The Picard group of a scheme, built from actual line bundles and sheaf isomorphisms. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

structure BundledLineBundle (X : Scheme.{u}) where
  sheaf : X.Modules
  isLineBundle : LineBundle.Construction.IsLineBundle sheaf

instance lineBundleSetoid (X : Scheme.{u}) : Setoid (BundledLineBundle X) where
  r L M := Nonempty (L.sheaf ≅ M.sheaf)
  iseqv :=
    { refl L := ⟨Iso.refl L.sheaf⟩
      symm := fun ⟨e⟩ ↦ ⟨e.symm⟩
      trans := fun ⟨e⟩ ⟨f⟩ ↦ ⟨e ≪≫ f⟩ }

def Picard (X : Scheme.{u}) := Quotient (lineBundleSetoid X)

def lineBundleClass {X : Scheme.{u}} (M : X.Modules) (hM : LineBundle.Construction.IsLineBundle M) : Picard X :=
  Quotient.mk _ ⟨M, hM⟩

theorem lineBundleClass_eq_iff {X : Scheme.{u}} {M N : X.Modules}
    (hM : LineBundle.Construction.IsLineBundle M) (hN : LineBundle.Construction.IsLineBundle N) :
    lineBundleClass M hM = lineBundleClass N hN ↔ Nonempty (M ≅ N) :=
  Quotient.eq

instance picardZero (X : Scheme.{u}) : Zero (Picard X) :=
  ⟨lineBundleClass (LineBundle.Construction.structureSheafModule X) (LineBundle.Construction.isLineBundle_structureSheaf X)⟩

instance picardAdd (X : Scheme.{u}) : Add (Picard X) where
  add := Quotient.map₂
    (fun L M ↦ ⟨SheafTensor.Construction.sheafTensor L.sheaf M.sheaf, TensorRestriction.Construction.isLineBundle_sheafTensor L.isLineBundle M.isLineBundle⟩)
    (fun _ _ ⟨e⟩ _ _ ⟨f⟩ ↦ ⟨SheafTensor.Construction.sheafTensorCongr e f⟩)

instance picardNeg (X : Scheme.{u}) : Neg (Picard X) where
  neg := Quotient.map
    (fun L ↦ ⟨SheafHomModule.Construction.lineBundleDual L.sheaf, LineBundleDual.Construction.isLineBundle_dual L.isLineBundle⟩)
    (fun _ _ ⟨e⟩ ↦ ⟨SheafHomFunctoriality.Construction.sheafHomCongr e (Iso.refl _)⟩)

instance picardSub (X : Scheme.{u}) : Sub (Picard X) := ⟨fun a b ↦ a + -b⟩

instance picardAddCommGroup (X : Scheme.{u}) : AddCommGroup (Picard X) where
  add_assoc a b c := Quotient.inductionOn₃ a b c fun L M N ↦
    Quotient.sound ⟨LineBundleAssociator.Construction.lineBundleTensorAssociator L.isLineBundle M.isLineBundle N.isLineBundle⟩
  zero_add a := Quotient.inductionOn a fun L ↦ Quotient.sound ⟨SheafTensor.Construction.sheafTensorUnitLeft L.sheaf⟩
  add_zero a := Quotient.inductionOn a fun L ↦ Quotient.sound ⟨SheafTensor.Construction.sheafTensorUnitRight L.sheaf⟩
  neg_add_cancel a := Quotient.inductionOn a fun L ↦ Quotient.sound ⟨LineBundleEvaluation.Construction.lineBundleDualTensorIso L.isLineBundle⟩
  add_comm a b := Quotient.inductionOn₂ a b fun L M ↦ Quotient.sound ⟨SheafTensor.Construction.sheafTensorComm L.sheaf M.sheaf⟩
  sub_eq_add_neg _ _ := rfl
  nsmul := nsmulRec
  zsmul := zsmulRec

theorem lineBundleClass_tensor {X : Scheme.{u}} {M N : X.Modules}
    (hM : LineBundle.Construction.IsLineBundle M) (hN : LineBundle.Construction.IsLineBundle N) :
    lineBundleClass (SheafTensor.Construction.sheafTensor M N) (TensorRestriction.Construction.isLineBundle_sheafTensor hM hN) =
      lineBundleClass M hM + lineBundleClass N hN := rfl

theorem lineBundleClass_dual {X : Scheme.{u}} {M : X.Modules} (hM : LineBundle.Construction.IsLineBundle M) :
    lineBundleClass (SheafHomModule.Construction.lineBundleDual M) (LineBundleDual.Construction.isLineBundle_dual hM) = -lineBundleClass M hM := rfl

theorem lineBundleClass_unit {X : Scheme.{u}} :
    lineBundleClass (LineBundle.Construction.structureSheafModule X) (LineBundle.Construction.isLineBundle_structureSheaf X) = (0 : Picard X) := rfl

theorem lineBundleClass_tensorPower {X : Scheme.{u}} {M : X.Modules} (hM : LineBundle.Construction.IsLineBundle M) (n : ℕ) :
    lineBundleClass (TensorRestriction.Construction.sheafTensorPower M n) (TensorRestriction.Construction.isLineBundle_sheafTensorPower hM n) =
      n • lineBundleClass M hM := by
  induction n with
  | zero => exact (zero_nsmul _).symm
  | succ n ih =>
    change lineBundleClass (TensorRestriction.Construction.sheafTensorPower M n) (TensorRestriction.Construction.isLineBundle_sheafTensorPower hM n) +
      lineBundleClass M hM = (n + 1) • lineBundleClass M hM
    rw [ih, add_nsmul, one_nsmul]

end

end OAI.ArithmeticGeometry.OrdinaryLocus.Openness.PicardEq.Construction

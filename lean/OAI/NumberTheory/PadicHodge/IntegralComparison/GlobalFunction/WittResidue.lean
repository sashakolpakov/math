import OAI.NumberTheory.PadicHodge.IntegralComparison.SmoothProper.GlobalFunctionConstants
import OAI.NumberTheory.PadicHodge.IntegralComparison.ZeroLevel.GlobalFunctionLinear

/-! # Witt Residue -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.GlobalFunction.WittResidue

noncomputable section

/-! The new crystalline classes reduce to their actual zeroth Witt coefficients in global regular functions. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry Opposite

universe u

variable (p : ℕ) [Fact p.Prime] (k : Type u) [Field k] [CharP k p]
  (X : Over (Spec (CommRingCat.of k)))

local notation "A" => OAI.NumberTheory.PadicHodge.IntegralComparison.SmoothProper.GlobalFunctionAlgebra.algebra k X
local notation "f" => OAI.NumberTheory.PadicHodge.IntegralComparison.Witt.Crystalline.wittStructureMap p k X

theorem frame_factor (U : X.left.Opens) (hU : IsAffineOpen U) :
    (ZeroLevel.AffineOpenSections.frame p k X U hU).obj.mapToX ≫ WittFactor.factor k X p =
      Spec.map (CommRingCat.ofHom (WittVector.constantCoeff : WittVector p A →+* A) ≫
        X.left.presheaf.map (homOfLE (show U ≤ ⊤ from le_top)).op ≫
          CommRingCat.ofHom (Ideal.Quotient.mk (⊥ : Ideal Γ(X.left, U)))) := by
  let r : CommRingCat.of (WittVector p A) ⟶ Γ(X.left, ⊤) := CommRingCat.ofHom WittVector.constantCoeff
  let s : Γ(X.left, ⊤) ⟶ Γ(X.left, U) := X.left.presheaf.map (homOfLE le_top).op
  let q : Γ(X.left, U) ⟶ CommRingCat.of (Γ(X.left, U) ⧸ (⊥ : Ideal Γ(X.left, U))) :=
    CommRingCat.ofHom (Ideal.Quotient.mk ⊥)
  change (Spec.map q ≫ hU.fromSpec) ≫ (X.left.toSpecΓ ≫ Spec.map r) = Spec.map (r ≫ s ≫ q)
  have h := congrArg (fun t => Spec.map q ≫ t ≫ Spec.map r) hU.fromSpec_toSpecΓ
  exact (Category.assoc _ _ _).trans
    ((congrArg (fun t => Spec.map q ≫ t) (Category.assoc hU.fromSpec X.left.toSpecΓ (Spec.map r)).symm).trans
      (h.trans (by rw [Spec.map_comp, Spec.map_comp, Category.assoc])))

theorem frame_residue (w : WittVector p A) (U : X.left.Opens) (hU : IsAffineOpen U) :
    Crystalline.EtaleResidue.residueRingMap (WittVector p A) (WittFactor.factor k X p)
      (ZeroLevel.AffineOpenSections.frame p k X U hU).obj w =
        Ideal.Quotient.mk (⊥ : Ideal Γ(X.left, U))
          (X.left.presheaf.map (homOfLE (show U ≤ ⊤ from le_top)).op (w.coeff 0)) := by
  have h := congrArg Spec.preimage (frame_factor p k X U hU)
  exact ConcreteCategory.congr_hom (h.trans (Spec.preimage_map _)) w

variable [Finite k] [IsProper X.hom] [Smooth X.hom] [Nonempty X.left]
  (hprojective : Projectivity.Construction.ProjectiveOver k X.hom)

theorem frame_value (w : WittVector p A) (U : X.left.Opens) (hU : IsAffineOpen U) :
    Crystalline.ConstantSections.value f (SmoothProper.GlobalFunctionConstants.sections p k X hprojective w)
      (ZeroLevel.AffineOpenSections.frame p k X U hU).obj =
        X.left.presheaf.map (homOfLE (show U ≤ ⊤ from le_top)).op (w.coeff 0) := by
  have h := (SmoothProper.GlobalFunctionConstants.value_reduction p k X hprojective w
    (ZeroLevel.AffineOpenSections.frame p k X U hU).obj).trans (frame_residue p k X w U hU)
  exact sub_eq_zero.mp (Ideal.mem_bot.mp (Ideal.Quotient.eq.mp h))

theorem global_value (w : WittVector p A) :
    ZeroLevel.GlobalFunctions.value p k X
      (BoundedCrystalline.CrystallineSections.restriction f 0
        (SmoothProper.GlobalFunctionConstants.sections p k X hprojective w)) = w.coeff 0 := by
  symm
  apply ZeroLevel.GlobalFunctions.unique p k X
  intro U hU
  exact (frame_value p k X hprojective w U hU).symm

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.GlobalFunction.WittResidue

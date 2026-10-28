import OAI.AlgebraicGeometry.Picard.Homomorphisms.SchemeGroup
import OAI.AlgebraicGeometry.Picard.Homomorphisms.MultilinearHom
import OAI.AlgebraicGeometry.Picard.Homomorphisms.LineBundleClasses

/-! # Tensor Power Group -/

namespace OAI.AlgebraicGeometry.Picard.Homomorphisms.TensorPowerGroup

noncomputable section

/-! Actual multilinear tensor powers agree with powers in the scheme Picard group. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

set_option backward.isDefEq.respectTransparency.types false

namespace Construction

universe u

variable {X : Scheme.{u}} {L M P Q : X.Modules}

def zeroMultilinearSourceEquiv (L M P : X.Modules) :
    AbelianModuli.HilbertConstruction.Tensor.Powers.SheafMultilinearMap L 0 P ≃ AbelianModuli.HilbertConstruction.Tensor.Powers.SheafMultilinearMap M 0 P where
  toFun b := b.precomp 0
  invFun b := b.precomp 0
  left_inv b := by
    ext U s
    change b.app U _ = b.app U s
    congr 1
    funext i
    exact Fin.elim0 i
  right_inv b := by
    ext U s
    change b.app U _ = b.app U s
    congr 1
    funext i
    exact Fin.elim0 i

theorem unit_isTensorPower_zero (L : X.Modules) : AbelianModuli.HilbertConstruction.Tensor.Powers.IsTensorPower L 0 (AbelianModuli.HilbertConstruction.Line.Bundles.structureModule X) := by
  obtain ⟨b, hb⟩ := UnitTensorPower.Construction.unit_isTensorPower X 0
  refine ⟨b.precomp (0 : L ⟶ AbelianModuli.HilbertConstruction.Line.Bundles.structureModule X), fun P => ?_⟩
  let e := zeroMultilinearSourceEquiv (AbelianModuli.HilbertConstruction.Line.Bundles.structureModule X) L P
  have he : (fun f : AbelianModuli.HilbertConstruction.Line.Bundles.structureModule X ⟶ P => (b.precomp (0 : L ⟶ AbelianModuli.HilbertConstruction.Line.Bundles.structureModule X)).postcomp f) =
      fun f => e (b.postcomp f) :=
    funext (fun f => (AbelianModuli.HilbertConstruction.Tensor.Powers.SheafMultilinearMap.precomp_postcomp b 0 f).symm)
  rw [he]
  exact e.bijective.comp (hb P)

def multilinearOutputFunctor (L : X.Modules) (n : ℕ) : X.Modules ⥤ Type u where
  obj P := AbelianModuli.HilbertConstruction.Tensor.Powers.SheafMultilinearMap L n P
  map f := TypeCat.ofHom (fun b => b.postcomp f)
  map_id P := by ext b U s; rfl
  map_comp f g := by ext b U s; rfl

def tensorPowerCorepresentable (L : X.Modules) (n : ℕ) :
    (multilinearOutputFunctor L n).CorepresentableBy (TensorPowerSheaf.Construction.tensorPowerSheaf L n) where
  homEquiv := TensorPowerSheaf.Construction.tensorPowerSheafHomEquiv L n _
  homEquiv_comp h f := by
    change TensorPowerSheaf.Construction.tensorPowerSheafHomEquiv L n _ (f ≫ h) = (TensorPowerSheaf.Construction.tensorPowerSheafHomEquiv L n _ f).postcomp h
    erw [← TensorPowerSheaf.Construction.tensorPowerSheafMultilinear_postcomp, ← TensorPowerSheaf.Construction.tensorPowerSheafMultilinear_postcomp,
      AbelianModuli.HilbertConstruction.Tensor.Powers.SheafMultilinearMap.postcomp_comp]

def tensorPowerSuccHomEquiv (L : X.Modules) (n : ℕ) (P : X.Modules) :
    (AbelianModuli.HilbertConstruction.Tensor.ProductSheaf.tensorModule (TensorPowerSheaf.Construction.tensorPowerSheaf L n) L ⟶ P) ≃ AbelianModuli.HilbertConstruction.Tensor.Powers.SheafMultilinearMap L (n + 1) P :=
  (TensorHom.Construction.tensorInternalHomEquiv (TensorPowerSheaf.Construction.tensorPowerSheaf L n) L P).trans
    ((TensorPowerSheaf.Construction.tensorPowerSheafHomEquiv L n (InternalHom.Construction.moduleInternalHom L P)).trans MultilinearHom.Construction.sheafMultilinearCurryRightEquiv.symm)

theorem tensorPowerSuccHomEquiv_apply (L : X.Modules) (n : ℕ)
    (f : AbelianModuli.HilbertConstruction.Tensor.ProductSheaf.tensorModule (TensorPowerSheaf.Construction.tensorPowerSheaf L n) L ⟶ P) (U : X.Opens) (s : Fin (n + 1) → Γ(L, U)) :
    (tensorPowerSuccHomEquiv L n P f).app U s =
      f.app U ((TensorAssociativity.Construction.tensorModuleBilinear (TensorPowerSheaf.Construction.tensorPowerSheaf L n) L).app U
        ((TensorPowerSheaf.Construction.tensorPowerSheafMultilinear L n).app U (Fin.init s)) (s (Fin.last n))) := by
  change TensorHom.Construction.internalHomEval L P U
      ((TensorPowerSheaf.Construction.tensorPowerSheafHomEquiv L n (InternalHom.Construction.moduleInternalHom L P)
        (TensorHom.Construction.sheafBilinearCurry (AbelianModuli.HilbertConstruction.Bilinear.Sheaves.SheafBilinearMap.tensorHomEquiv (TensorPowerSheaf.Construction.tensorPowerSheaf L n) L P f))).app U
          (Fin.init s)) (s (Fin.last n)) = _
  rw [← TensorPowerSheaf.Construction.tensorPowerSheafMultilinear_postcomp]
  change (AbelianModuli.HilbertConstruction.Bilinear.Sheaves.SheafBilinearMap.tensorHomEquiv (TensorPowerSheaf.Construction.tensorPowerSheaf L n) L P f).app U
      ((TensorPowerSheaf.Construction.tensorPowerSheaf L n).presheaf.map (𝟙 U).op
        ((TensorPowerSheaf.Construction.tensorPowerSheafMultilinear L n).app U (Fin.init s))) (s (Fin.last n)) = _
  rw [op_id, (TensorPowerSheaf.Construction.tensorPowerSheaf L n).presheaf.map_id, AddCommGrpCat.id_apply,
    TensorAssociativity.Construction.tensorModuleBilinear_postcomp]
  rfl

def tensorPowerSuccCorepresentable (L : X.Modules) (n : ℕ) :
    (multilinearOutputFunctor L (n + 1)).CorepresentableBy (AbelianModuli.HilbertConstruction.Tensor.ProductSheaf.tensorModule (TensorPowerSheaf.Construction.tensorPowerSheaf L n) L) where
  homEquiv := tensorPowerSuccHomEquiv L n _
  homEquiv_comp h f := by
    change tensorPowerSuccHomEquiv L n _ (f ≫ h) = (tensorPowerSuccHomEquiv L n _ f).postcomp h
    ext U s
    change (tensorPowerSuccHomEquiv L n _ (f ≫ h)).app U s =
      h.app U ((tensorPowerSuccHomEquiv L n _ f).app U s)
    rw [tensorPowerSuccHomEquiv_apply, tensorPowerSuccHomEquiv_apply]
    rfl

def tensorPowerSuccIso (L : X.Modules) (n : ℕ) :
    TensorPowerSheaf.Construction.tensorPowerSheaf L (n + 1) ≅ AbelianModuli.HilbertConstruction.Tensor.ProductSheaf.tensorModule (TensorPowerSheaf.Construction.tensorPowerSheaf L n) L :=
  (tensorPowerCorepresentable L (n + 1)).uniqueUpToIso (tensorPowerSuccCorepresentable L n)

theorem tensorPowerClass_zero (q : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.IsoClass X) : LineBundleClasses.Construction.tensorPowerClass 0 q = 1 := by
  induction q using Quotient.inductionOn with
  | h L =>
    exact Quotient.sound
      ((TensorPowerSheaf.Construction.tensorPowerSheaf_isTensorPower L.sheaf 0).unique (unit_isTensorPower_zero L.sheaf))

theorem tensorPowerClass_succ (n : ℕ) (q : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.IsoClass X) :
    LineBundleClasses.Construction.tensorPowerClass (n + 1) q = LineBundleClasses.Construction.tensorPowerClass n q * q := by
  induction q using Quotient.inductionOn with
  | h L => exact Quotient.sound ⟨tensorPowerSuccIso L.sheaf n⟩

theorem tensorPowerClass_eq_pow (n : ℕ) (q : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.IsoClass X) : LineBundleClasses.Construction.tensorPowerClass n q = q ^ n := by
  induction n with
  | zero => exact (tensorPowerClass_zero q).trans (pow_zero q).symm
  | succ n ih => rw [tensorPowerClass_succ, ih, pow_succ]

theorem frobeniusPullbackClass_eq_pow (p : ℕ) (hp : p.Prime) (hX : (p : Γ(X, ⊤)) = 0)
    (q : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.IsoClass X) :
    AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass (Frobenius.Construction.absoluteFrobenius p hp X hX) q = q ^ p :=
  (LineBundleClasses.Construction.frobeniusPullbackClass_eq_tensorPowerClass p hp hX q).trans (tensorPowerClass_eq_pow p q)

end Construction

end

end OAI.AlgebraicGeometry.Picard.Homomorphisms.TensorPowerGroup

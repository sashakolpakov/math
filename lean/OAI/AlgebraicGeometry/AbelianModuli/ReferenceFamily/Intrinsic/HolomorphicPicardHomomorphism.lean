import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.HolomorphicTensor
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.HolomorphicTrivialClass

/-! # Holomorphic Picard Homomorphism -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.HolomorphicPicardHomomorphism

noncomputable section

/-! The native holomorphic class is an actual homomorphism from
algebraic line-bundle isomorphism classes, with sheaf duals mapping to
negatives. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

variable (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)

local instance nativeHolomorphicPicardHom_cohomologyGroup :
    AddCommGroup (DivisorClass.Chern.Holomorphic.Connecting.holomorphicUnitCohomology V.analyticModel V.analyticSpace) :=
  Cech.Add.cechClassAddCommGroup (X := TopCat.of V.analyticSpace) (DivisorClass.Chern.Holomorphic.Sheaves.holomorphicUnitsSheaf V.analyticModel V.analyticSpace) 1

theorem nativeHolomorphicPicardClass_tensor (a b : HilbertConstruction.Line.Bundles.LineBundle.IsoClass V.carrier) :
    HolomorphicIsoClass.nativeHolomorphicPicardClass V (HilbertConstruction.Line.Bundles.LineBundle.tensorClass a b) =
      HolomorphicIsoClass.nativeHolomorphicPicardClass V a + HolomorphicIsoClass.nativeHolomorphicPicardClass V b := by
  induction a using Quotient.inductionOn with
  | h L =>
    induction b using Quotient.inductionOn with
    | h K => exact HolomorphicTensor.nativeHolomorphicLineClass_tensor V L K

def nativeHolomorphicPicardAddHom : Additive (HilbertConstruction.Line.Bundles.LineBundle.IsoClass V.carrier) →+
    DivisorClass.Chern.Holomorphic.Connecting.holomorphicUnitCohomology V.analyticModel V.analyticSpace where
  toFun a := HolomorphicIsoClass.nativeHolomorphicPicardClass V a.toMul
  map_zero' := HolomorphicTrivialClass.nativeHolomorphicPicardClass_one V
  map_add' a b := nativeHolomorphicPicardClass_tensor V a.toMul b.toMul

theorem nativeHolomorphicLineClass_dual (L : HilbertConstruction.Line.Bundles.LineBundle V.carrier) :
    HolomorphicLineClass.nativeHolomorphicLineClass V (Picard.Homomorphisms.LineBundleDual.Construction.lineBundleDual L) = -HolomorphicLineClass.nativeHolomorphicLineClass V L :=
  map_neg (nativeHolomorphicPicardAddHom V) (Additive.ofMul (HilbertConstruction.Line.Bundles.LineBundle.classOf L))

theorem nativeHolomorphicLineClass_tensor_dual (L K : HilbertConstruction.Line.Bundles.LineBundle V.carrier) :
    HolomorphicLineClass.nativeHolomorphicLineClass V (L.tensor (Picard.Homomorphisms.LineBundleDual.Construction.lineBundleDual K)) =
      HolomorphicLineClass.nativeHolomorphicLineClass V L - HolomorphicLineClass.nativeHolomorphicLineClass V K :=
  (HolomorphicTensor.nativeHolomorphicLineClass_tensor V L (Picard.Homomorphisms.LineBundleDual.Construction.lineBundleDual K)).trans
    ((congrArg (fun x => HolomorphicLineClass.nativeHolomorphicLineClass V L + x) (nativeHolomorphicLineClass_dual V K)).trans
      (sub_eq_add_neg _ _).symm)

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.HolomorphicPicardHomomorphism

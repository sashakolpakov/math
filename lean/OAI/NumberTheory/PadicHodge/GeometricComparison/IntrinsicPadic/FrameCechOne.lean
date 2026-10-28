import OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.FrameInjective
import OAI.NumberTheory.PadicHodge.GeometricComparison.Cech.TotalOneQuasiIso

/-! # Frame Cech One -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.FrameCechOne.IntrinsicPadicFrameCechHOne

noncomputable section

/-! The actual native frame-to-injective section comparison induces an
isomorphism on H¹ of its original Cech total complexes. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry Opposite Simplicial

variable (p : ℕ) [Fact p.Prime]
  (X : Over (Spec (CommRingCat.of ℤ_[p]))) [IsProper X.hom] [Smooth X.hom] [X.left.IsSeparated]
  (Y : Over (Spec (CommRingCat.of (ZMod p)))) [IsSeparated Y.hom]
  (f : Y.left ⟶ X.left)
  (hp : IsPullback f Y.hom X.hom (Spec.map (CommRingCat.ofHom (PadicInt.toZMod : ℤ_[p] →+* ZMod p))))
  (n : ℕ)

local notation "Rcoeff" => OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.ExactRestriction.Coeff (B := WittVector p (ZMod p))
local notation "coverOpens" => OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.CechSliceResolution.IntrinsicPadicCechSliceResolution.opens p X
local notation "coverNerve" => OAI.NumberTheory.PadicHodge.IntegralComparison.NonemptyCechNerve.nerve coverOpens

variable (J : InjectiveResolution (IntegralComparison.BoundedCrystalline.CrystallineCohomology.structureSheaf (p := p)
  (J := Ideal.span {(p : WittVector p (ZMod p))})
  (δ := AlgebraicGeometry.Crystalline.Cohomology.Witt.DividedPowers.WittDividedPowers.wittDividedPowers p (ZMod p))
  (IntegralComparison.Witt.Crystalline.wittStructureMap p (ZMod p) Y) n))

def map := Cech.TotalOneQuasiIso.CechTotalHOneQuasiIso.map.{1, 2} Rcoeff coverNerve
  (FrameInjective.IntrinsicPadicFrameInjectiveComparison.map p X Y f hp n J)

theorem intersection_quasiIso (m : ℕ) (t : Fin (m + 1) → Integral.EtaleAffineCover.IntegralEtaleAffineCover.Index ℤ_[p] X) :
    QuasiIso ((((evaluation X.left.affineOpensᵒᵖ (ModuleCat.{2} Rcoeff)).obj
      (op (((coverNerve).obj (op ⦋m⦌)).obj t))).mapHomologicalComplex (.up ℕ)).map
        (FrameInjective.IntrinsicPadicFrameInjectiveComparison.map p X Y f hp n J)) := by
  let I : X.left.affineOpens := ((coverNerve).obj (op ⦋m⦌)).obj t
  have hi : I.val ≤ Integral.EtaleAffineCover.IntegralEtaleAffineCoverSections.opens ℤ_[p] X (t 0) :=
    leOfHom (Pi.π (coverOpens ∘ t) 0)
  exact FrameInjective.IntrinsicPadicFrameInjectiveComparison.evaluation_quasiIso p X Y f hp n J I (t 0) hi

theorem quasiIsoAt : QuasiIsoAt (IntrinsicPadicFrameCechHOne.map p X Y f hp n J) 1 :=
  Cech.TotalOneQuasiIso.CechTotalHOneQuasiIso.quasiIsoAt.{1, 2} Rcoeff coverNerve
    (FrameInjective.IntrinsicPadicFrameInjectiveComparison.map p X Y f hp n J)
    (intersection_quasiIso p X Y f hp n J)

end

end OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.FrameCechOne.IntrinsicPadicFrameCechHOne

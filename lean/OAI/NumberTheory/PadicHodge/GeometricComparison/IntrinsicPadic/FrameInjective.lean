import OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.FrameDiagonalIso
import OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.PadicDiagonalCechComparison
import OAI.NumberTheory.PadicHodge.GeometricComparison.QuasiIsoLeft

/-! # Frame Injective -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.FrameInjective.IntrinsicPadicFrameInjectiveComparison

noncomputable section

/-! The actual native frame de Rham diagram maps to the original global
injective-resolution sections, with local quasi-isomorphism on the coordinate cover. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry Opposite

variable (p : ℕ) [Fact p.Prime]
  (X : Over (Spec (CommRingCat.of ℤ_[p]))) [IsProper X.hom] [Smooth X.hom] [X.left.IsSeparated]
  (Y : Over (Spec (CommRingCat.of (ZMod p)))) [IsSeparated Y.hom]
  (f : Y.left ⟶ X.left)
  (hp : IsPullback f Y.hom X.hom (Spec.map (CommRingCat.ofHom (PadicInt.toZMod : ℤ_[p] →+* ZMod p))))
  (n : ℕ)

local notation "Rcoeff" => OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.ExactRestriction.Coeff (B := WittVector p (ZMod p))
local notation "S" => OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.SectionBifunctor.IntrinsicPadicSectionBifunctor.sections p X Y f n

variable (J : InjectiveResolution (IntegralComparison.BoundedCrystalline.CrystallineCohomology.structureSheaf (p := p)
  (J := Ideal.span {(p : WittVector p (ZMod p))})
  (δ := AlgebraicGeometry.Crystalline.Cohomology.Witt.DividedPowers.WittDividedPowers.wittDividedPowers p (ZMod p))
  (IntegralComparison.Witt.Crystalline.wittStructureMap p (ZMod p) Y) n))

def map : AlgebraicGeometry.Crystalline.Cohomology.ComplexAssemblyQuasi.ComplexAssembly.complex (.up ℕ) (FrameDiagonalMap.IntrinsicPadicFrameDiagonalMap.source p X Y f hp n) ⟶
    ((S).mapHomologicalComplex (.up ℕ)).obj J.cocomplex :=
  FrameDiagonalMap.IntrinsicPadicFrameDiagonalMap.map p X Y f hp n ≫ PadicDiagonalCechComparison.IntrinsicPadicDiagonalCechComparison.map p X Y f hp n J

variable (I : X.left.affineOpens) (i : Integral.EtaleAffineCover.IntegralEtaleAffineCover.Index ℤ_[p] X)
  (hi : I.val ≤ Integral.EtaleAffineCover.IntegralEtaleAffineCoverSections.opens ℤ_[p] X i)

include hi in
theorem evaluation_quasiIso : QuasiIso
    (((PadicDiagonalCechComparison.IntrinsicPadicDiagonalCechComparison.evaluate p X I).mapHomologicalComplex (.up ℕ)).map
      (IntrinsicPadicFrameInjectiveComparison.map p X Y f hp n J)) := by
  let ha : IsIso ((FrameDiagonalMap.IntrinsicPadicFrameDiagonalMap.transformation p X Y f hp n).app (op I)) :=
    FrameDiagonalIso.IntrinsicPadicFrameDiagonalIso.isIso p X Y f hp n I i hi
  let hb := PadicDiagonalCechComparison.IntrinsicPadicDiagonalCechComparison.evaluation_quasiIso p X Y f hp n J I i hi
  change QuasiIso ((FrameDiagonalMap.IntrinsicPadicFrameDiagonalMap.transformation p X Y f hp n).app (op I) ≫
    (((PadicDiagonalCechComparison.IntrinsicPadicDiagonalCechComparison.evaluate p X I).mapHomologicalComplex (.up ℕ)).map
      (PadicDiagonalCechComparison.IntrinsicPadicDiagonalCechComparison.map p X Y f hp n J)))
  exact QuasiIsoLeft.QuasiIsoComposeIsomorphism.left _ _ ha hb

end

end OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.FrameInjective.IntrinsicPadicFrameInjectiveComparison

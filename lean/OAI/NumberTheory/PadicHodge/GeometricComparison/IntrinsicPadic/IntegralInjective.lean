import OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.ReducedDeRhamIso
import OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.FrameInjective

/-! # Integral Injective -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.IntegralInjective.IntrinsicPadicIntegralInjectiveComparison

noncomputable section

/-! The canonical integral de Rham coefficient quotient maps into the
original global crystalline injective-resolution sections, locally by quasi-isomorphisms. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry Opposite

variable (p : ℕ) [Fact p.Prime]
  (X : Over (Spec (CommRingCat.of ℤ_[p]))) [IsProper X.hom] [Smooth X.hom] [X.left.IsSeparated]
  (Y : Over (Spec (CommRingCat.of (ZMod p)))) [IsSeparated Y.hom]
  (f : Y.left ⟶ X.left)
  (hp : IsPullback f Y.hom X.hom (Spec.map (CommRingCat.ofHom (PadicInt.toZMod : ℤ_[p] →+* ZMod p))))
  (n : ℕ)

local notation "Rcoeff" => OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.ExactRestriction.Coeff (B := WittVector p (ZMod p))
local notation "S" => OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.SectionBifunctor.IntrinsicPadicSectionBifunctor.sections p X Y f n

def coefficients : ModuleCat (WittVector p (ZMod p)) ⥤ ModuleCat.{2} Rcoeff :=
  IntegralComparison.Crystalline.RelativeResolution.coefficientFunctor ⋙ ModuleCat.uliftFunctor.{2, 1} Rcoeff

instance coefficients_additive : (coefficients p).Additive := by
  dsimp only [coefficients]
  infer_instance

def source := ReducedDeRhamMap.IntrinsicPadicReducedDeRhamMap.source p X n ⋙ (coefficients p).mapHomologicalComplex (.up ℕ)

def transformation : source p X n ⟶ FrameDiagonalMap.IntrinsicPadicFrameDiagonalMap.source p X Y f hp n :=
  Functor.whiskerRight (ReducedDeRhamMap.IntrinsicPadicReducedDeRhamMap.pdTransformation p X Y f hp n)
    ((coefficients p).mapHomologicalComplex (.up ℕ))

variable (J : InjectiveResolution (IntegralComparison.BoundedCrystalline.CrystallineCohomology.structureSheaf (p := p)
  (J := Ideal.span {(p : WittVector p (ZMod p))})
  (δ := AlgebraicGeometry.Crystalline.Cohomology.Witt.DividedPowers.WittDividedPowers.wittDividedPowers p (ZMod p))
  (IntegralComparison.Witt.Crystalline.wittStructureMap p (ZMod p) Y) n))

def map : AlgebraicGeometry.Crystalline.Cohomology.ComplexAssemblyQuasi.ComplexAssembly.complex (.up ℕ) (source p X n) ⟶
    ((S).mapHomologicalComplex (.up ℕ)).obj J.cocomplex :=
  AlgebraicGeometry.Crystalline.Cohomology.ComplexAssemblyQuasi.ComplexAssembly.map (.up ℕ) (transformation p X Y f hp n) ≫
    FrameInjective.IntrinsicPadicFrameInjectiveComparison.map p X Y f hp n J

variable (I : X.left.affineOpens) (i : Integral.EtaleAffineCover.IntegralEtaleAffineCover.Index ℤ_[p] X)
  (hi : I.val ≤ Integral.EtaleAffineCover.IntegralEtaleAffineCoverSections.opens ℤ_[p] X i)

include hi in
theorem evaluation_quasiIso : QuasiIso
    (((PadicDiagonalCechComparison.IntrinsicPadicDiagonalCechComparison.evaluate p X I).mapHomologicalComplex (.up ℕ)).map
      (IntrinsicPadicIntegralInjectiveComparison.map p X Y f hp n J)) := by
  have ha := ReducedDeRhamIso.IntrinsicPadicReducedDeRhamIso.pd_component_isIso p X Y f hp n I i hi
  have hb := FrameInjective.IntrinsicPadicFrameInjectiveComparison.evaluation_quasiIso p X Y f hp n J I i hi
  exact QuasiIsoLeft.QuasiIsoComposeIsomorphism.mappedLeft
    ((coefficients p).mapHomologicalComplex (.up ℕ))
    ((ReducedDeRhamMap.IntrinsicPadicReducedDeRhamMap.pdTransformation p X Y f hp n).app (op I)) _ ha hb

end

end OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.IntegralInjective.IntrinsicPadicIntegralInjectiveComparison

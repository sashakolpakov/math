import OAI.NumberTheory.PadicHodge.IntegralComparison.Cech.PresheafMapQuasiIso
import OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.ZariskiSectionQuasiIso
import OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.SectionBifunctor

/-! # Cech Injective Quasi Iso -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.IntrinsicPadic.CechInjectiveQuasiIso.IntrinsicOpen

noncomputable section

/-! The unchanged p-adic model-to-injective map is a quasi-isomorphism
on the native open-section Čech total in every degree. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry Opposite

variable (p : ℕ) [Fact p.Prime]
  (X : Over (Spec (CommRingCat.of ℤ_[p]))) [IsProper X.hom] [Smooth X.hom] [X.left.IsSeparated]
  (Y : Over (Spec (CommRingCat.of (ZMod p)))) [IsSeparated Y.hom] (f : Y.left ⟶ X.left)
  (hp : IsPullback f Y.hom X.hom
    (Spec.map (CommRingCat.ofHom (PadicInt.toZMod : ℤ_[p] →+* ZMod p)))) (n : ℕ)
  (I : InjectiveResolution (BoundedCrystalline.CrystallineCohomology.structureSheaf (p := p)
    (J := Ideal.span {(p : WittVector p (ZMod p))})
    (δ := AlgebraicGeometry.Crystalline.Cohomology.Witt.DividedPowers.WittDividedPowers.wittDividedPowers p (ZMod p))
    (Witt.Crystalline.wittStructureMap p (ZMod p) Y) n))

local notation "R" => OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.ExactRestriction.Coeff (B := WittVector p (ZMod p))
local notation "U" => OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.CechSliceResolution.IntrinsicPadicCechSliceResolution.opens p X
local notation "S" => OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.SectionBifunctor.IntrinsicPadicSectionBifunctor.sections p X Y f n
local notation "a" => OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.CechInjective.IntrinsicPadicCechInjectiveComparison.map p X Y f hp n I

theorem evaluation_quasiIso (j : ℕ)
    (b : Fin (j+1) → GeometricComparison.Integral.EtaleAffineCover.IntegralEtaleAffineCover.Index ℤ_[p] X) :
    QuasiIso ((((CategoryTheory.evaluation X.left.affineOpensᵒᵖ (ModuleCat.{2} R)).obj
      (op (∏ᶜ (U ∘ b)))).mapHomologicalComplex (.up ℕ)).map
        (((S).mapHomologicalComplex (.up ℕ)).map a)) :=
  GeometricComparison.IntrinsicPadic.ZariskiSectionQuasiIso.IntrinsicPadicCechZariskiSectionQuasiIso.evaluation_quasiIso p X Y f hp n
    (∏ᶜ (U ∘ b)) I (b 0) (leOfHom (Pi.π (U ∘ b) 0))

theorem quasiIso : QuasiIso ((GeometricComparison.CechCone.TotalFunctor.CechConeTotalFunctor.functor U).map
    (HomologicalComplex.complexOfFunctorsToFunctorToComplex.map
      (((S).mapHomologicalComplex (.up ℕ)).map a))) := Cech.PresheafMapQuasiIso.quasiIso.{1,0,2} R U
  (((S).mapHomologicalComplex (.up ℕ)).map a)
  (evaluation_quasiIso p X Y f hp n I)

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.IntrinsicPadic.CechInjectiveQuasiIso.IntrinsicOpen

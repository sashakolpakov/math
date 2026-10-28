import OAI.NumberTheory.PadicHodge.IntegralComparison.EtaleZero.ResolutionSections
import OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedFrame.ResolutionMapCoherence
import OAI.NumberTheory.PadicHodge.IntegralComparison.HomologyMapPrecomposition

/-! # Resolution Map Coherence -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.EtaleZero.ResolutionMapCoherence

noncomputable section

/-! The original affine de Rham section comparison respects maps of its injective resolutions. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

open OAI.NumberTheory.PadicHodge.IntegralComparison.Witt.Crystalline OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.Presentation

universe u

variable (p : ℕ) [Fact p.Prime] (k C σ : Type u) [Field k] [Fintype k] [CharP k p]
  [CommRing C] [Algebra k C] [Fintype σ] [Algebra (MvPolynomial σ k) C]
  [IsScalarTower k (MvPolynomial σ k) C] [Algebra.Etale (MvPolynomial σ k) C]

local notation "R" => OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.ExactRestriction.Coeff (B := WittVector p k)

variable (I I' : InjectiveResolution (BoundedCrystalline.CrystallineCohomology.structureSheaf (p := p)
    (J := Ideal.span {(p : WittVector p k)})
    (δ := AlgebraicGeometry.Crystalline.Cohomology.Witt.DividedPowers.WittDividedPowers.wittDividedPowers p k) (Witt.Crystalline.wittStructureMap p k (Crystalline.Presentation.affineScheme k C)) 0))
  (e : I.cocomplex ⟶ I'.cocomplex) (he : I.ι ≫ e = I'.ι)

include he in
theorem frame_homology (i : ℕ) :
    HomologicalComplex.homologyMap (ResolutionSections.frameMap p k C σ I ≫
      ((Sheaf.PresheafSectionComplex.sectionFunctor.{u + 1, u, u + 1, u + 2} R
        (BoundedCrystalline.Site.topology (p := p)
        (J := Ideal.span {(p : WittVector p k)})
        (δ := AlgebraicGeometry.Crystalline.Cohomology.Witt.DividedPowers.WittDividedPowers.wittDividedPowers p k) (Witt.Crystalline.wittStructureMap p k (Crystalline.Presentation.affineScheme k C)) 0)).mapHomologicalComplex (.up ℕ)).map e) i =
    HomologicalComplex.homologyMap (ResolutionSections.frameMap p k C σ I') i :=
  let _ : QuasiIso (Bounded.RelativeSheafComplex.augmentation (Witt.Crystalline.wittStructureMap p k (Crystalline.Presentation.affineScheme k C)) 0 (ZeroLevel.LevelFrame.boundedFrame p k C)) :=
    BoundedEtale.ZeroResolution.augmentation_quasiIso p k C σ
  BoundedFrame.ResolutionMapCoherence.homology (Witt.Crystalline.wittStructureMap p k (Crystalline.Presentation.affineScheme k C)) 0 (ZeroLevel.LevelFrame.boundedFrame p k C) I I' e he i

include he in
theorem deRham_homology (i : ℕ) :
    HomologicalComplex.homologyMap (ResolutionSections.map p k C σ I ≫
      ((Sheaf.PresheafSectionComplex.sectionFunctor.{u + 1, u, u + 1, u + 2} R
        (BoundedCrystalline.Site.topology (p := p)
        (J := Ideal.span {(p : WittVector p k)})
        (δ := AlgebraicGeometry.Crystalline.Cohomology.Witt.DividedPowers.WittDividedPowers.wittDividedPowers p k) (Witt.Crystalline.wittStructureMap p k (Crystalline.Presentation.affineScheme k C)) 0)).mapHomologicalComplex (.up ℕ)).map e) i =
    HomologicalComplex.homologyMap (ResolutionSections.map p k C σ I') i :=
  (congrArg (fun a => HomologicalComplex.homologyMap a i) (Category.assoc _ _ _)).trans
    (HomologyMapPrecomposition.equality (DeRham.Comparison.frameIso p k C).inv _ _ i
      (frame_homology p k C σ I I' e he i))

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.EtaleZero.ResolutionMapCoherence

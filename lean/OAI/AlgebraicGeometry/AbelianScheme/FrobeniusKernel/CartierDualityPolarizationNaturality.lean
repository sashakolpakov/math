import OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.CartierDualityWeilNaturality
import OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.CartierDualityPolarizationAdjoints
import OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.SheafPairingTransport

/-! # Cartier Duality Polarization Naturality -/

namespace OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.CartierDualityPolarizationNaturality

noncomputable section

/-! Actual preservation of the polarization map preserves CartierDuality's canonical
polarization pairing on all test schemes. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj

attribute [local instance] Picard.Homomorphisms.UnbundledDualGroup.Construction.UnbundledPicard.dualPicardGroup_commutative

namespace Construction

variable {S : Scheme} (A B : CartierDuality.PolarizedTorsion.AbelianScheme S)
variable (ellA : CartierDuality.PolarizedTorsion.Polarization A) (ellB : CartierDuality.PolarizedTorsion.Polarization B)
variable (n : ℕ) (hn : 0 < n) (f : A.toOver ⟶ B.toOver) [IsMonHom f]

theorem e56PolarizationPairing_morphism
    (h : f ≫ ellB.map ≫
      (IntrinsicCartierNaturality.Construction.nativePicardPullbackGroup A.toOver B.toOver f ellA.dual ellB.dual).hom.hom = ellA.map)
    (T : Over S) (x y : (A.torsionSheaf n).obj.obj (.op T)) :
    CartierDuality.SheafEvaluation.Construction.Schemes.sheafCharacterValue (B.torsionSheaf n) T
      ((ellB.torsionPairing n hn).rightAdjoint.hom.app (.op T)
        ((CartierDuality.SheafTorsionMaps.Construction.Schemes.torsionSheafMap (CartierDuality.RepresentedMorphisms.Construction.Schemes.representedFppfAbMap (IntrinsicMultiplicationNaturality.Construction.nativeAbelianGroupHom A.toOver B.toOver f)) n).hom.app (.op T) y))
      ((CartierDuality.SheafTorsionMaps.Construction.Schemes.torsionSheafMap (CartierDuality.RepresentedMorphisms.Construction.Schemes.representedFppfAbMap (IntrinsicMultiplicationNaturality.Construction.nativeAbelianGroupHom A.toOver B.toOver f)) n).hom.app (.op T) x) =
    CartierDuality.SheafEvaluation.Construction.Schemes.sheafCharacterValue (A.torsionSheaf n) T ((ellA.torsionPairing n hn).rightAdjoint.hom.app (.op T) y) x := by
  let a := IntrinsicMultiplicationNaturality.Construction.nativeAbelianGroupHom A.toOver B.toOver f
  let b := CartierDualityPolarizationAdjoints.Construction.e56PolarizationGroupHom B ellB
  let d := IntrinsicCartierNaturality.Construction.nativePicardPullbackGroup A.toOver B.toOver f ellA.dual ellB.dual
  let c := CartierDualityPolarizationAdjoints.Construction.e56PolarizationGroupHom A ellA
  have hg : a ≫ b ≫ d = c := by
    apply Grp.hom_ext
    exact h
  have hr : CartierDuality.RepresentedMorphisms.Construction.Schemes.representedFppfAbMap a ≫ CartierDuality.RepresentedMorphisms.Construction.Schemes.representedFppfAbMap b ≫ CartierDuality.RepresentedMorphisms.Construction.Schemes.representedFppfAbMap d =
      CartierDuality.RepresentedMorphisms.Construction.Schemes.representedFppfAbMap c :=
    (congrArg (fun t => CartierDuality.RepresentedMorphisms.Construction.Schemes.representedFppfAbMap a ≫ t) (CartierDuality.RepresentedMorphisms.Construction.Schemes.representedFppfAbMap_comp b d).symm).trans
      ((CartierDuality.RepresentedMorphisms.Construction.Schemes.representedFppfAbMap_comp a (b ≫ d)).symm.trans (congrArg (fun t => CartierDuality.RepresentedMorphisms.Construction.Schemes.representedFppfAbMap t) hg))
  have ht : CartierDuality.SheafTorsionMaps.Construction.Schemes.torsionSheafMap (CartierDuality.RepresentedMorphisms.Construction.Schemes.representedFppfAbMap a) n ≫
      CartierDuality.SheafTorsionMaps.Construction.Schemes.torsionSheafMap (CartierDuality.RepresentedMorphisms.Construction.Schemes.representedFppfAbMap b) n ≫ CartierDuality.SheafTorsionMaps.Construction.Schemes.torsionSheafMap (CartierDuality.RepresentedMorphisms.Construction.Schemes.representedFppfAbMap d) n =
      CartierDuality.SheafTorsionMaps.Construction.Schemes.torsionSheafMap (CartierDuality.RepresentedMorphisms.Construction.Schemes.representedFppfAbMap c) n :=
    (congrArg (fun t => CartierDuality.SheafTorsionMaps.Construction.Schemes.torsionSheafMap (CartierDuality.RepresentedMorphisms.Construction.Schemes.representedFppfAbMap a) n ≫ t)
      (IntrinsicTorsionSheafFunctor.Construction.torsionSheafMap_comp (CartierDuality.RepresentedMorphisms.Construction.Schemes.representedFppfAbMap b) (CartierDuality.RepresentedMorphisms.Construction.Schemes.representedFppfAbMap d) n).symm).trans
      ((IntrinsicTorsionSheafFunctor.Construction.torsionSheafMap_comp (CartierDuality.RepresentedMorphisms.Construction.Schemes.representedFppfAbMap a)
        (CartierDuality.RepresentedMorphisms.Construction.Schemes.representedFppfAbMap b ≫ CartierDuality.RepresentedMorphisms.Construction.Schemes.representedFppfAbMap d) n).symm.trans
          (congrArg (fun t => CartierDuality.SheafTorsionMaps.Construction.Schemes.torsionSheafMap t n) hr))
  exact SheafPairingTransport.Construction.sheafPolarizationPairing_transport (ellA.weilPairing n hn) (ellB.weilPairing n hn)
    (CartierDuality.SheafTorsionMaps.Construction.Schemes.torsionSheafMap (CartierDuality.RepresentedMorphisms.Construction.Schemes.representedFppfAbMap a) n) (CartierDuality.SheafTorsionMaps.Construction.Schemes.torsionSheafMap (CartierDuality.RepresentedMorphisms.Construction.Schemes.representedFppfAbMap d) n)
    (ellA.torsionMap n) (ellB.torsionMap n)
    (CartierDualityWeilNaturality.Construction.e56WeilPairing_morphism A B ellA ellB n hn f) ht T x y

end Construction

end

end OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.CartierDualityPolarizationNaturality

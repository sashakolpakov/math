import OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.PicardCanonicalBaseChange
import OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.CartierPicardBaseChange
import OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.IntrinsicWeilCharacterPoints
import OAI.AlgebraicGeometry.AbelianScheme.CartierDuality.TorsionBaseChange

/-! # Intrinsic Weil Base Change -/

namespace OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.IntrinsicWeilBaseChange

noncomputable section

/-! The actual CartierDuality Weil pairing commutes with arbitrary source base
change, on native torsion points and the original multiplicative group. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj

attribute [local instance] Picard.Homomorphisms.GroupDescent.Construction.groupHom_pow_isMonHom
attribute [local instance] Picard.Homomorphisms.UnbundledDualGroup.Construction.UnbundledPicard.dualPicardGroup_commutative

namespace Construction

attribute [local instance] BaseChange.Construction.pulledBackGroup

variable {S S' : Scheme} (s : S' ⟶ S) (A : Over S) [GrpObj A] [IsCommMonObj A]
    [Smooth A.hom] [IsProper A.hom] [GeometricallyConnected A.hom]
    [Smooth ((Over.pullback s).obj A).hom] [IsProper ((Over.pullback s).obj A).hom]
    [GeometricallyConnected ((Over.pullback s).obj A).hom]
    (D : Picard.Homomorphisms.UnbundledDualData.Construction.UnbundledPicard.DualData A) (ell : A ⟶ D.withPicardGroup.abelian) [IsMonHom ell]
    [IsFinite ell.left] [Flat ell.left] [Surjective ell.left]
    (ell' : (Over.pullback s).obj A ⟶ (D.pullback s).withPicardGroup.abelian) [IsMonHom ell']
    [IsFinite ell'.left] [Flat ell'.left] [Surjective ell'.left]
    (n : ℕ) (hn : 0 < n)
    [IsFinite ((𝟙 A : A ⟶ A) ^ n).left] [Flat ((𝟙 A : A ⟶ A) ^ n).left]
    [Surjective ((𝟙 A : A ⟶ A) ^ n).left] [LocallyOfFinitePresentation ((𝟙 A : A ⟶ A) ^ n).left]
    [IsFinite ((𝟙 ((Over.pullback s).obj A) : (Over.pullback s).obj A ⟶ (Over.pullback s).obj A) ^ n).left]
    [Flat ((𝟙 ((Over.pullback s).obj A) : (Over.pullback s).obj A ⟶ (Over.pullback s).obj A) ^ n).left]
    [Surjective ((𝟙 ((Over.pullback s).obj A) : (Over.pullback s).obj A ⟶ (Over.pullback s).obj A) ^ n).left]
    [LocallyOfFinitePresentation ((𝟙 ((Over.pullback s).obj A) : (Over.pullback s).obj A ⟶ (Over.pullback s).obj A) ^ n).left]
    (C : CartierDuality.GroupRepresentatives.Construction.Schemes.CharacterGroupRepresentation S (Grp.mk (Picard.Homomorphisms.Kernel.Construction.kernelScheme ((𝟙 A) ^ n))))
    (C' : CartierDuality.GroupRepresentatives.Construction.Schemes.CharacterGroupRepresentation S' (Grp.mk (Picard.Homomorphisms.Kernel.Construction.kernelScheme ((𝟙 ((Over.pullback s).obj A)) ^ n))))

theorem nativeWeilPointValue_baseChange (Q : Over S')
    (x : Q ⟶ Picard.Homomorphisms.Kernel.Construction.kernelScheme ((𝟙 ((Over.pullback s).obj A)) ^ n))
    (y : Q ⟶ TorsionQuotient.SubgroupFunctor.torsionScheme (D.pullback s).withPicardGroup.abelian n)
    (y0 : (Over.map s).obj Q ⟶ TorsionQuotient.SubgroupFunctor.torsionScheme D.withPicardGroup.abelian n)
    (hy : Picard.Homomorphisms.UnbundledBaseChangePoints.Construction.UnbundledPicard.baseChangePointsEquiv D.abelian s Q
      (y ≫ TorsionQuotient.SubgroupFunctor.torsionι (D.pullback s).withPicardGroup.abelian n) =
        y0 ≫ TorsionQuotient.SubgroupFunctor.torsionι D.withPicardGroup.abelian n) :
    IntrinsicWeilCharacterPoints.Construction.nativeWeilPointValue ((Over.pullback s).obj A) (D.pullback s) ell' n hn C' Q x y =
      CartierDuality.EvaluationBaseChange.Construction.Schemes.multiplicativeGroupPointBaseChange s Q
        (IntrinsicWeilCharacterPoints.Construction.nativeWeilPointValue A D ell n hn C ((Over.map s).obj Q)
          (CartierPicardBaseChange.Construction.nativeKernelBaseChangeAlongPoint s ((𝟙 A) ^ n) ((𝟙 ((Over.pullback s).obj A)) ^ n)
            (CartierDuality.TorsionBaseChange.Construction.CoprimeTorsion.power_baseChange s A n).symm Q x) y0) := by
  let f := (𝟙 A : A ⟶ A) ^ n
  let f' := (𝟙 ((Over.pullback s).obj A) : (Over.pullback s).obj A ⟶ (Over.pullback s).obj A) ^ n
  have hf : f' = (Over.pullback s).map f := (CartierDuality.TorsionBaseChange.Construction.CoprimeTorsion.power_baseChange s A n).symm
  let c := CartierPicardBaseChange.Construction.nativeCartierBaseChangeAlong s f f' hf C C'
  let x0 := CartierPicardBaseChange.Construction.nativeKernelBaseChangeAlongPoint s f f' hf Q x
  obtain ⟨d, hd⟩ := IntrinsicWeilCharacterPoints.Construction.nativeCartierTorsion_surjective_points A D ell n hn C ((Over.map s).obj Q) y0
  let dp : Q ⟶ (C.baseChange s).dual.X := (Over.mapPullbackAdj s).homEquiv Q C.dual.X d
  have hdp : C.baseChangeOriginalPoint s Q dp = d :=
    ((Over.mapPullbackAdj s).homEquiv Q C.dual.X).symm_apply_apply d
  have hd0 : d ≫ CartierDuality.ParameterizedCharacterLines.Construction.KernelCharacters.cartierToPicard f D.withPicardGroup C =
      y0 ≫ TorsionQuotient.SubgroupFunctor.torsionι D.withPicardGroup.abelian n := by
    exact (congrArg (fun z => d ≫ z) (CartierDuality.CharacterTorsionFactor.Construction.KernelCharacters.cartierToPicardTorsion_inclusion f D.withPicardGroup n
      (CartierDuality.CharacterTorsionFactor.Construction.KernelCharacters.multiplicationKernelPoint_pow A n) C)).symm.trans
      ((Category.assoc _ _ _).symm.trans (congrArg (fun z => z ≫ TorsionQuotient.SubgroupFunctor.torsionι D.withPicardGroup.abelian n) hd))
  have hc := PicardCanonicalBaseChange.Construction.nativeCartierPicard_baseChange_canonical s f f' hf C' D C
  have hnew : (dp ≫ c.hom.hom) ≫ CartierDuality.ParameterizedCharacterLines.Construction.KernelCharacters.cartierToPicard f' (D.pullback s).withPicardGroup C' =
      y ≫ TorsionQuotient.SubgroupFunctor.torsionι (D.pullback s).withPicardGroup.abelian n := by
    apply (Picard.Homomorphisms.UnbundledBaseChangePoints.Construction.UnbundledPicard.baseChangePointsEquiv D.abelian s Q).injective
    have hs := (Category.assoc dp c.hom.hom _).trans (congrArg (fun z => dp ≫ z) hc)
    have hp := (Over.mapPullbackAdj s).homEquiv_naturality_right_symm dp
      (CartierDuality.ParameterizedCharacterLines.Construction.KernelCharacters.cartierToPicard f D.withPicardGroup C)
    exact (congrArg (Picard.Homomorphisms.UnbundledBaseChangePoints.Construction.UnbundledPicard.baseChangePointsEquiv D.abelian s Q) hs).trans
      (hp.trans ((congrArg (fun z => z ≫ CartierDuality.ParameterizedCharacterLines.Construction.KernelCharacters.cartierToPicard f D.withPicardGroup C) hdp).trans
        (hd0.trans hy.symm)))
  have hval := CartierPicardBaseChange.Construction.nativeCartierBaseChangeAlong_evaluation s f f' hf C C' Q dp x
  have hold := IntrinsicWeilCharacterPoints.Construction.nativeWeilPointValue_of_character A D ell n hn C ((Over.map s).obj Q) d x0 y0 hd0
  exact (IntrinsicWeilCharacterPoints.Construction.nativeWeilPointValue_of_character ((Over.pullback s).obj A) (D.pullback s) ell' n hn C'
    Q (dp ≫ c.hom.hom) x y hnew).trans
    (hval.trans ((congrArg (fun z => CartierDuality.EvaluationBaseChange.Construction.Schemes.multiplicativeGroupPointBaseChange s Q
      (C.evaluationValue ((Over.map s).obj Q) z x0)) hdp).trans
      (congrArg (CartierDuality.EvaluationBaseChange.Construction.Schemes.multiplicativeGroupPointBaseChange s Q) hold.symm)))

end Construction

end

end OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.IntrinsicWeilBaseChange

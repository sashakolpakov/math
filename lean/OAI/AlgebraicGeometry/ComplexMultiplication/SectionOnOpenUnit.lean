import OAI.AlgebraicTopology.Support.RelativeCohomologyOpenTransport

/-! # Section On Open Unit -/

namespace OAI.AlgebraicGeometry.ComplexMultiplication.SectionOnOpenUnit

noncomputable section

section

/-! # The actual open-embedding transport preserves relative-cohomology sheafification units -/

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open _root_.CategoryTheory Limits _root_.TopologicalSpace _root_.Topology Opposite OAI.AlgebraicTopology.Singular

variable {X Y : TopCat.{0}} (f : Y ⟶ X) (hf : IsOpenEmbedding f)
  (S : Set X) (B : Set Y) (hB : f ⁻¹' S = B) (n : ℕ)

theorem relativeSheafOpenIso_unit :
    AlgebraicTopology.Support.RelativeCohomologySheaf.Singular.supportRelativeCohomologyToSheaf Y B n ≫
      (AlgebraicTopology.Support.RelativeCohomologyOpenTransport.Singular.supportRelativeCohomologySheafOpenIso f hf S B hB n).hom.hom =
    (AlgebraicTopology.Support.RelativeCohomologyOpenTransport.Singular.supportRelativeCohomologyPresheafOpenIso f hf S B hB n).inv ≫
      Functor.whiskerLeft hf.functor.op (AlgebraicTopology.Support.RelativeCohomologySheaf.Singular.supportRelativeCohomologyToSheaf X S n) := by
  let : hf.functor.IsContinuous (Opens.grothendieckTopology Y)
      (Opens.grothendieckTopology X) := hf.functor_isContinuous
  let : hf.functor.IsCocontinuous (Opens.grothendieckTopology Y)
      (Opens.grothendieckTopology X) := (AlgebraicTopology.Sheaf.OpenSheafification.Topology.IsOpenEmbedding.functor_isCocontinuous hf)
  let e := AlgebraicTopology.Support.RelativeCohomologyOpenTransport.Singular.supportRelativeCohomologyPresheafOpenIso f hf S B hB n
  have hu := hf.functor.toSheafify_pullbackSheafificationCompatibility
    AddCommGrpCat (Opens.grothendieckTopology Y) (Opens.grothendieckTopology X)
    (AlgebraicTopology.Support.RelativeCohomologySheaf.Singular.supportRelativeCohomologyPresheaf X S n)
  have hn := toSheafify_naturality (Opens.grothendieckTopology Y) e.inv
  change toSheafify (Opens.grothendieckTopology Y) _ ≫
    sheafifyMap (Opens.grothendieckTopology Y) e.inv ≫
      (AlgebraicTopology.Support.RelativeCohomologyOpenTransport.Singular.supportOpenEmbeddingSheafificationIso f hf
        (AlgebraicTopology.Support.RelativeCohomologySheaf.Singular.supportRelativeCohomologyPresheaf X S n)).hom.hom = _
  have hu' : toSheafify (Opens.grothendieckTopology Y)
      (hf.functor.op ⋙ AlgebraicTopology.Support.RelativeCohomologySheaf.Singular.supportRelativeCohomologyPresheaf X S n) ≫
      (AlgebraicTopology.Support.RelativeCohomologyOpenTransport.Singular.supportOpenEmbeddingSheafificationIso f hf
        (AlgebraicTopology.Support.RelativeCohomologySheaf.Singular.supportRelativeCohomologyPresheaf X S n)).hom.hom =
    Functor.whiskerLeft hf.functor.op (AlgebraicTopology.Support.RelativeCohomologySheaf.Singular.supportRelativeCohomologyToSheaf X S n) := by
    simpa only [AlgebraicTopology.Support.RelativeCohomologyOpenTransport.Singular.supportOpenEmbeddingSheafificationIso,
      AlgebraicTopology.Support.RelativeCohomologySheaf.Singular.supportRelativeCohomologyToSheaf] using! hu
  rw [← Category.assoc, ← hn, Category.assoc, hu']

end

/-! # Transport of actual relative classes preserves the actual sheafification unit -/

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open _root_.CategoryTheory Limits _root_.TopologicalSpace _root_.Topology Opposite OAI.AlgebraicTopology.Singular

variable {X Y : TopCat.{0}} (f : Y ⟶ X) (hf : IsOpenEmbedding f)
  (S : Set X) (B : Set Y) (hB : f ⁻¹' S = B) (n : ℕ) (U : Opens X)
  (hU : hf.functor.obj ⊤ = U)

/-- The actual pair-image inverse and the actual equality-of-opens restriction. -/
def relativeClassOnOpen
    (a : AlgebraicTopology.Singular.Cohomology.RelativeCohomology ℚ (AlgebraicTopology.LocalHomology.FundamentalClass.Singular.neighborhoodSupportComplementPair (Set.univ : Set Y) B) n) :
    AlgebraicTopology.Singular.Cohomology.RelativeCohomology ℚ (AlgebraicTopology.LocalHomology.FundamentalClass.Singular.neighborhoodSupportComplementPair (U : Set X) S) n :=
  (AlgebraicTopology.Support.RelativeCohomologySheaf.Singular.supportRelativeCohomologyPresheaf X S n).map (eqToHom hU.symm).op
    ((AlgebraicTopology.Support.RelativeCohomologyOpenTransport.Singular.supportRelativeCohomologyPresheafOpenIso f hf S B hB n).inv.app (op ⊤) a)

theorem relativeSectionOnOpen_unit
    (a : AlgebraicTopology.Singular.Cohomology.RelativeCohomology ℚ (AlgebraicTopology.LocalHomology.FundamentalClass.Singular.neighborhoodSupportComplementPair (Set.univ : Set Y) B) n) :
    AlgebraicTopology.Support.RelativeCohomologyOpenTransport.Singular.supportRelativeCohomologySectionOnOpen f hf S B hB n U hU
      ((AlgebraicTopology.Support.RelativeCohomologySheaf.Singular.supportRelativeCohomologyToSheaf Y B n).app (op ⊤) a) =
    (AlgebraicTopology.Support.RelativeCohomologySheaf.Singular.supportRelativeCohomologyToSheaf X S n).app (op U)
      (relativeClassOnOpen f hf S B hB n U hU a) := by
  have hc : (AlgebraicTopology.Support.RelativeCohomologyOpenTransport.Singular.supportRelativeCohomologySheafOpenIso f hf S B hB n).hom.hom.app (op ⊤)
      ((AlgebraicTopology.Support.RelativeCohomologySheaf.Singular.supportRelativeCohomologyToSheaf Y B n).app (op ⊤) a) =
    (AlgebraicTopology.Support.RelativeCohomologySheaf.Singular.supportRelativeCohomologyToSheaf X S n).app (op (hf.functor.obj ⊤))
      ((AlgebraicTopology.Support.RelativeCohomologyOpenTransport.Singular.supportRelativeCohomologyPresheafOpenIso f hf S B hB n).inv.app (op ⊤) a) := by
    have h := congrArg (fun g => g.app (op ⊤)) (relativeSheafOpenIso_unit f hf S B hB n)
    simpa only [NatTrans.comp_app, Functor.whiskerLeft_app, ConcreteCategory.comp_apply]
      using! ConcreteCategory.congr_hom h a
  have hn := ConcreteCategory.congr_hom
    ((AlgebraicTopology.Support.RelativeCohomologySheaf.Singular.supportRelativeCohomologyToSheaf X S n).naturality (eqToHom hU.symm).op)
    ((AlgebraicTopology.Support.RelativeCohomologyOpenTransport.Singular.supportRelativeCohomologyPresheafOpenIso f hf S B hB n).inv.app (op ⊤) a)
  unfold AlgebraicTopology.Support.RelativeCohomologyOpenTransport.Singular.supportRelativeCohomologySectionOnOpen AlgebraicTopology.Support.RelativeCohomologyOpenTransport.Singular.supportRelativeCohomologySectionOpenImage
    relativeClassOnOpen
  change (AlgebraicTopology.Support.RelativeCohomologySheaf.Singular.supportRelativeCohomologySheaf X S n).presheaf.map (eqToHom hU.symm).op
    ((AlgebraicTopology.Support.RelativeCohomologyOpenTransport.Singular.supportRelativeCohomologySheafOpenIso f hf S B hB n).hom.hom.app (op ⊤)
      ((AlgebraicTopology.Support.RelativeCohomologySheaf.Singular.supportRelativeCohomologyToSheaf Y B n).app (op ⊤) a)) = _
  rw [hc]
  exact hn.symm

end

end OAI.AlgebraicGeometry.ComplexMultiplication.SectionOnOpenUnit

import OAI.AlgebraicGeometry.AbelianScheme.CartierDuality.SheafBlocks
import OAI.AlgebraicGeometry.AbelianScheme.CartierDuality.RepresentedMorphisms

/-! # Sheaf Kernel Annihilator -/

namespace OAI.AlgebraicGeometry.Isogenies.NeighborCounting.SheafKernelAnnihilator

noncomputable section

/-! Sectionwise kernel detection and character restriction, retaining
every test scheme and every further base change. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

open OAI.AlgebraicGeometry.AbelianScheme.CartierDuality.RepresentedMorphisms.Construction.Schemes

theorem sheaf_square_kernel_iff {S : Scheme} {G H K L : AbelianScheme.CartierDuality.CommutativeSheavesAb.Construction.Schemes.FppfAb S}
    (a : G ⟶ H) (b : G ⟶ K) (p : H ⟶ L) (q : K ⟶ L) [Mono p] [Mono q]
    (hs : a ≫ p = b ≫ q) (T : Over S) (x : G.obj.obj (.op T)) :
    a.hom.app (.op T) x = 1 ↔ b.hom.app (.op T) x = 1 := by
  have hp : Function.Injective (p.hom.app (.op T)) :=
    (CommGrpCat.mono_iff_injective (p.hom.app (.op T))).mp inferInstance
  have hq : Function.Injective (q.hom.app (.op T)) :=
    (CommGrpCat.mono_iff_injective (q.hom.app (.op T))).mp inferInstance
  have hv := congrArg (fun w => w.hom.app (.op T) x) hs
  change p.hom.app (.op T) (a.hom.app (.op T) x) =
    q.hom.app (.op T) (b.hom.app (.op T) x) at hv
  constructor
  · intro ha
    apply hq
    exact hv.symm.trans ((congrArg (p.hom.app (.op T)) ha).trans
      ((p.hom.app (.op T)).hom.map_one.trans (q.hom.app (.op T)).hom.map_one.symm))
  · intro hb
    apply hp
    exact hv.trans ((congrArg (q.hom.app (.op T)) hb).trans
      ((q.hom.app (.op T)).hom.map_one.trans (p.hom.app (.op T)).hom.map_one.symm))

theorem sheaf_restriction_character_zero_iff {S : Scheme} {G H K : AbelianScheme.CartierDuality.CommutativeSheavesAb.Construction.Schemes.FppfAb S}
    (e : AbelianScheme.CartierDuality.SheafEvaluation.Construction.Schemes.BilinearPairing G K) (i : H ⟶ G) (T : Over S) (x : K.obj.obj (.op T)) :
    ((AbelianScheme.CartierDuality.CommutativeSheavesAb.Construction.Schemes.cartierDualSheafFunctor S).map i.op).hom.app (.op T)
        (e.rightAdjoint.hom.app (.op T) x) = 1 ↔
      ∀ (U : Over S) (t : U ⟶ T) (y : H.obj.obj (.op U)),
        AbelianScheme.CartierDuality.SheafEvaluation.Construction.Schemes.sheafCharacterValue G U (e.rightAdjoint.hom.app (.op U) (K.obj.map t.op x))
          (i.hom.app (.op U) y) = 1 := by
  let d := e.rightAdjoint ≫ (AbelianScheme.CartierDuality.CommutativeSheavesAb.Construction.Schemes.cartierDualSheafFunctor S).map i.op
  have hv (U : Over S) (t : U ⟶ T) (y : H.obj.obj (.op U)) :
      AbelianScheme.CartierDuality.SheafEvaluation.Construction.Schemes.sheafCharacterValue H U ((AbelianScheme.CartierDuality.CommutativeSheavesAb.Construction.Schemes.cartierDualSheaf H).obj.map t.op (d.hom.app (.op T) x)) y =
        AbelianScheme.CartierDuality.SheafEvaluation.Construction.Schemes.sheafCharacterValue G U (e.rightAdjoint.hom.app (.op U) (K.obj.map t.op x))
          (i.hom.app (.op U) y) := by
    exact (congrArg (fun z => AbelianScheme.CartierDuality.SheafEvaluation.Construction.Schemes.sheafCharacterValue H U z y)
      (d.hom.naturality_apply t.op x).symm).trans
        (AbelianScheme.CartierDuality.SheafEvaluation.Construction.Schemes.cartierDualSheafMap_value i U (e.rightAdjoint.hom.app (.op U) (K.obj.map t.op x)) y)
  constructor
  · intro hz U t y
    have he : AbelianScheme.CartierDuality.SheafEvaluation.Construction.Schemes.sheafCharacterValue H U ((AbelianScheme.CartierDuality.CommutativeSheavesAb.Construction.Schemes.cartierDualSheaf H).obj.map t.op (d.hom.app (.op T) x)) y = 1 := by
      erw [show d.hom.app (.op T) x = 1 from hz]
      exact congrArg (fun z => AbelianScheme.CartierDuality.SheafEvaluation.Construction.Schemes.sheafCharacterValue H U z y)
        ((AbelianScheme.CartierDuality.CommutativeSheavesAb.Construction.Schemes.cartierDualSheaf H).obj.map t.op).hom.map_one
    exact (hv U t y).symm.trans he
  · intro hz
    change d.hom.app (.op T) x = 1
    apply NatTrans.ext
    funext V
    apply GrpCat.hom_ext
    apply MonoidHom.ext
    intro y
    exact (AbelianScheme.CartierDuality.SheafEvaluation.Construction.Schemes.sheafCharacterValue_restrict H T (d.hom.app (.op T) x) V.unop y).symm.trans
      ((hv V.unop.left V.unop.hom y).trans (hz V.unop.left V.unop.hom y))

end

end OAI.AlgebraicGeometry.Isogenies.NeighborCounting.SheafKernelAnnihilator

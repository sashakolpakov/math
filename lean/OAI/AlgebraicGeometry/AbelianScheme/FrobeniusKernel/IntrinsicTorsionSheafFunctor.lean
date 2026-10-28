import OAI.AlgebraicGeometry.AbelianScheme.CartierDuality.SheafTorsionMaps

/-! # Intrinsic Torsion Sheaf Functor -/

namespace OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.IntrinsicTorsionSheafFunctor.Construction

noncomputable section

/-! Functoriality of the actual sheaf kernels of multiplication. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

open OAI.AlgebraicGeometry.AbelianScheme.CartierDuality.SheafTorsionMaps.Construction.Schemes

theorem torsionSheafMap_comp {S : Scheme} {F G H : CartierDuality.CommutativeSheavesAb.Construction.Schemes.FppfAb S}
    (f : F ⟶ G) (g : G ⟶ H) (n : ℕ) :
    CartierDuality.SheafTorsionMaps.Construction.Schemes.torsionSheafMap (f ≫ g) n = CartierDuality.SheafTorsionMaps.Construction.Schemes.torsionSheafMap f n ≫ CartierDuality.SheafTorsionMaps.Construction.Schemes.torsionSheafMap g n := by
  apply equalizer.hom_ext
  exact (CartierDuality.SheafTorsionMaps.Construction.Schemes.torsionSheafMap_inclusion (f ≫ g) n).trans
    ((Category.assoc (kernel.ι (CartierDuality.TorsionSheaves.Construction.Schemes.sheafPower F n)) f g).symm.trans
      ((congrArg (fun t => t ≫ g) (CartierDuality.SheafTorsionMaps.Construction.Schemes.torsionSheafMap_inclusion f n).symm).trans
        ((Category.assoc (CartierDuality.SheafTorsionMaps.Construction.Schemes.torsionSheafMap f n) (kernel.ι (CartierDuality.TorsionSheaves.Construction.Schemes.sheafPower G n)) g).trans
          ((congrArg (fun t => CartierDuality.SheafTorsionMaps.Construction.Schemes.torsionSheafMap f n ≫ t)
            (CartierDuality.SheafTorsionMaps.Construction.Schemes.torsionSheafMap_inclusion g n).symm).trans
              (Category.assoc (CartierDuality.SheafTorsionMaps.Construction.Schemes.torsionSheafMap f n) (CartierDuality.SheafTorsionMaps.Construction.Schemes.torsionSheafMap g n)
                (kernel.ι (CartierDuality.TorsionSheaves.Construction.Schemes.sheafPower H n))).symm))))

theorem torsionSheafMap_id {S : Scheme} (F : CartierDuality.CommutativeSheavesAb.Construction.Schemes.FppfAb S) (n : ℕ) :
    CartierDuality.SheafTorsionMaps.Construction.Schemes.torsionSheafMap (𝟙 F) n = 𝟙 (CartierDuality.TorsionSheaves.Construction.Schemes.torsionFppfAb F n) := by
  apply equalizer.hom_ext
  exact (CartierDuality.SheafTorsionMaps.Construction.Schemes.torsionSheafMap_inclusion (𝟙 F) n).trans
    ((Category.comp_id (kernel.ι (CartierDuality.TorsionSheaves.Construction.Schemes.sheafPower F n))).trans
      (Category.id_comp (kernel.ι (CartierDuality.TorsionSheaves.Construction.Schemes.sheafPower F n))).symm)

theorem torsionSheafMap_square {S : Scheme} {F G H I : CartierDuality.CommutativeSheavesAb.Construction.Schemes.FppfAb S}
    (a : F ⟶ G) (b : H ⟶ I) (f : F ⟶ H) (g : G ⟶ I)
    (h : a ≫ g = f ≫ b) (n : ℕ) :
    CartierDuality.SheafTorsionMaps.Construction.Schemes.torsionSheafMap a n ≫ CartierDuality.SheafTorsionMaps.Construction.Schemes.torsionSheafMap g n =
      CartierDuality.SheafTorsionMaps.Construction.Schemes.torsionSheafMap f n ≫ CartierDuality.SheafTorsionMaps.Construction.Schemes.torsionSheafMap b n :=
  (torsionSheafMap_comp a g n).symm.trans
    ((congrArg (fun t => CartierDuality.SheafTorsionMaps.Construction.Schemes.torsionSheafMap t n) h).trans (torsionSheafMap_comp f b n))

end

end OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.IntrinsicTorsionSheafFunctor.Construction

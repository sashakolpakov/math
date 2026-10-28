import OAI.AlgebraicGeometry.Comparison.Betti.Godement.Bicomplex

/-! # Total Naturality -/

namespace OAI.AlgebraicGeometry.Comparison.Betti.Godement.TotalNaturality

noncomputable section

/-! Naturality of the original total Godement augmentation on cochain complexes. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.HomologicalComplex₂

variable {X : TopCat.{0}}
  {K L : CochainComplex (TopCat.Sheaf (ModuleCat.{0} ℂ) X) ℕ}

def godementTotalMap (f : K ⟶ L) : Bicomplex.godementTotal K ⟶ Bicomplex.godementTotal L :=
  total.map (((Bicomplex.godementFunctor X).mapHomologicalComplex (.up ℕ)).map f) (.up ℕ)

theorem godementTotalAugmentation_naturality (f : K ⟶ L) :
    Bicomplex.godementTotalAugmentation K ≫ godementTotalMap f = f ≫ Bicomplex.godementTotalAugmentation L := by
  apply HomologicalComplex.Hom.ext
  funext n
  change ((Functor.stalkFamilyUnit X).app (K.X n) ≫ (Bicomplex.godementBicomplex X K).ιTotal
      (.up ℕ) n 0 n rfl) ≫
        (total.map (((Bicomplex.godementFunctor X).mapHomologicalComplex (.up ℕ)).map f) (.up ℕ)).f n =
    f.f n ≫ ((Functor.stalkFamilyUnit X).app (L.X n) ≫
      (Bicomplex.godementBicomplex X L).ιTotal (.up ℕ) n 0 n rfl)
  have h : (Functor.stalkFamilyUnit X).app (K.X n) ≫
      ((((Bicomplex.godementFunctor X).mapHomologicalComplex (.up ℕ)).map f).f n).f 0 =
        f.f n ≫ (Functor.stalkFamilyUnit X).app (L.X n) :=
    ((Functor.stalkFamilyUnit X).naturality (f.f n)).symm
  exact (Category.assoc _ _ _).trans
    ((congrArg (fun a => (Functor.stalkFamilyUnit X).app (K.X n) ≫ a)
      (ιTotal_map (Bicomplex.godementBicomplex X K) (Bicomplex.godementBicomplex X L)
        (((Bicomplex.godementFunctor X).mapHomologicalComplex (.up ℕ)).map f)
        (.up ℕ) n 0 n rfl)).trans
      ((Category.assoc _ _ _).symm.trans
        ((congrArg (fun a => a ≫ (Bicomplex.godementBicomplex X L).ιTotal (.up ℕ) n 0 n rfl) h).trans
          (Category.assoc _ _ _))))

theorem godementTotalMap_id (K : CochainComplex (TopCat.Sheaf (ModuleCat.{0} ℂ) X) ℕ) :
    godementTotalMap (𝟙 K) = 𝟙 (Bicomplex.godementTotal K) := by
  exact (congrArg (fun a => total.map a (.up ℕ))
    (((Bicomplex.godementFunctor X).mapHomologicalComplex (.up ℕ)).map_id K)).trans
      (total.map_id _ _)

theorem godementTotalMap_comp {M : CochainComplex (TopCat.Sheaf (ModuleCat.{0} ℂ) X) ℕ}
    (f : K ⟶ L) (g : L ⟶ M) :
    godementTotalMap (f ≫ g) = godementTotalMap f ≫ godementTotalMap g := by
  exact (congrArg (fun a => total.map a (.up ℕ))
    (((Bicomplex.godementFunctor X).mapHomologicalComplex (.up ℕ)).map_comp f g)).trans
      (total.map_comp _ _ _)

end

end OAI.AlgebraicGeometry.Comparison.Betti.Godement.TotalNaturality

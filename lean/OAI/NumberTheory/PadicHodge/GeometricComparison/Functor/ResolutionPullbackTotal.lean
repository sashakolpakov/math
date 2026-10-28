import OAI.NumberTheory.PadicHodge.GeometricComparison.Functor.ResolutionTotal
import OAI.NumberTheory.PadicHodge.GeometricComparison.Finite.TotalIso

/-! # Resolution Pullback Total -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.Functor.ResolutionPullbackTotal.FunctorResolutionPullbackTotal

noncomputable section

/-! Actual inverse-image maps of resolution functors induce augmentation-compatible maps on their total complexes. -/

open _root_.CategoryTheory Limits

universe u v u' v'

variable {C : Type u} [Category.{v} C] [Abelian C] [HasCoproducts.{0} C]
  {D : Type u'} [Category.{v'} D] [Abelian D] [HasCoproducts.{0} D]
  (F : C ⥤ D) [F.Additive]
  (T : C ⥤ CochainComplex C ℕ) [T.Additive]
  (N : D ⥤ CochainComplex D ℕ) [N.Additive]
  (a : T ⋙ F.mapHomologicalComplex (.up ℕ) ⟶ F ⋙ N)

def bicomplexMap (K : CochainComplex C ℕ) :
    AlgebraicGeometry.Comparison.Betti.TotalComplexFunctor.mapBicomplex F (ResolutionBicomplex.FunctorResolutionBicomplex.bicomplex T K) ⟶
      ResolutionBicomplex.FunctorResolutionBicomplex.bicomplex N ((F.mapHomologicalComplex (.up ℕ)).obj K) :=
  (NatTrans.mapHomologicalComplex a (.up ℕ)).app K

def map (K : CochainComplex C ℕ) :
    (F.mapHomologicalComplex (.up ℕ)).obj (ResolutionTotal.FunctorResolutionTotal.total T K) ⟶
      ResolutionTotal.FunctorResolutionTotal.total N ((F.mapHomologicalComplex (.up ℕ)).obj K) :=
  (AlgebraicGeometry.Comparison.Betti.Finite.TotalFunctor.finiteTotalComparisonIso F (ResolutionBicomplex.FunctorResolutionBicomplex.bicomplex T K)).inv ≫
    HomologicalComplex₂.total.map (bicomplexMap F T N a K) (.up ℕ)

theorem map_inclusion (K : CochainComplex C ℕ) (q p n : ℕ) (h : q + p = n) :
    F.map ((ResolutionBicomplex.FunctorResolutionBicomplex.bicomplex T K).ιTotal (.up ℕ) q p n h) ≫
        (AlgebraicGeometry.Comparison.Betti.Finite.TotalFunctor.finiteTotalComparisonIso F (ResolutionBicomplex.FunctorResolutionBicomplex.bicomplex T K)).inv.f n =
      (AlgebraicGeometry.Comparison.Betti.TotalComplexFunctor.mapBicomplex F (ResolutionBicomplex.FunctorResolutionBicomplex.bicomplex T K)).ιTotal (.up ℕ) q p n h := by
  let e := (HomologicalComplex.eval D (.up ℕ) n).mapIso
    (AlgebraicGeometry.Comparison.Betti.Finite.TotalFunctor.finiteTotalComparisonIso F (ResolutionBicomplex.FunctorResolutionBicomplex.bicomplex T K))
  exact e.comp_inv_eq.mpr (AlgebraicGeometry.Comparison.Betti.Finite.TotalFunctor.ι_finiteTotalComparisonComponent F
    (ResolutionBicomplex.FunctorResolutionBicomplex.bicomplex T K) q p n h).symm

variable (η : CochainComplex.single₀ C ⟶ T) (θ : CochainComplex.single₀ D ⟶ N)
  (ha : ∀ P, F.map ((η.app P).f 0) ≫ (a.app P).f 0 = (θ.app (F.obj P)).f 0)

include ha in
theorem augmentation (K : CochainComplex C ℕ) :
    (F.mapHomologicalComplex (.up ℕ)).map (ResolutionTotal.FunctorResolutionTotal.edge T η K) ≫ FunctorResolutionPullbackTotal.map F T N a K =
      ResolutionTotal.FunctorResolutionTotal.edge N θ ((F.mapHomologicalComplex (.up ℕ)).obj K) := by
  ext q : 1
  let B := ResolutionBicomplex.FunctorResolutionBicomplex.bicomplex T K
  let M := AlgebraicGeometry.Comparison.Betti.TotalComplexFunctor.mapBicomplex F B
  let E := ResolutionBicomplex.FunctorResolutionBicomplex.bicomplex N ((F.mapHomologicalComplex (.up ℕ)).obj K)
  let e := (AlgebraicGeometry.Comparison.Betti.Finite.TotalFunctor.finiteTotalComparisonIso F B).inv.f q
  let b := (HomologicalComplex₂.total.map (bicomplexMap F T N a K) (.up ℕ)).f q
  have hc : F.map (B.ιTotal (.up ℕ) q 0 q rfl) ≫ (e ≫ b) =
      (a.app (K.X q)).f 0 ≫ E.ιTotal (.up ℕ) q 0 q rfl :=
    (Category.assoc _ _ _).symm.trans
      ((congrArg (fun k => k ≫ b) (map_inclusion F T K q 0 q rfl)).trans
        (HomologicalComplex₂.ιTotal_map M E (bicomplexMap F T N a K) (.up ℕ) q 0 q rfl))
  change F.map ((η.app (K.X q)).f 0 ≫ B.ιTotal (.up ℕ) q 0 q rfl) ≫ (e ≫ b) =
    (θ.app (F.obj (K.X q))).f 0 ≫ E.ιTotal (.up ℕ) q 0 q rfl
  exact (congrArg (fun k => k ≫ (e ≫ b)) (F.map_comp _ _)).trans
    ((Category.assoc _ _ _).trans
      ((congrArg (fun k => F.map ((η.app (K.X q)).f 0) ≫ k) hc).trans
        ((Category.assoc _ _ _).symm.trans
          (congrArg (fun k => k ≫ E.ιTotal (.up ℕ) q 0 q rfl) (ha (K.X q))))))

end

end OAI.NumberTheory.PadicHodge.GeometricComparison.Functor.ResolutionPullbackTotal.FunctorResolutionPullbackTotal

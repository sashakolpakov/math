import OAI.NumberTheory.PadicHodge.GeometricComparison.Functor.ResolutionBicomplex

/-! # Resolution Total -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.Functor.ResolutionTotal.FunctorResolutionTotal

noncomputable section

/-! The total augmentation of an actual natural resolution functor is natural on complexes. -/

open _root_.CategoryTheory Limits

universe u v

variable {C : Type u} [Category.{v} C] [Abelian C] [HasCoproducts.{0} C]
  (G : C ⥤ CochainComplex C ℕ) [G.Additive]
  (η : CochainComplex.single₀ C ⟶ G)

def total (K : CochainComplex C ℕ) : CochainComplex C ℕ :=
  (ResolutionBicomplex.FunctorResolutionBicomplex.bicomplex G K).total (.up ℕ)

def map {K L : CochainComplex C ℕ} (f : K ⟶ L) : FunctorResolutionTotal.total G K ⟶ FunctorResolutionTotal.total G L :=
  HomologicalComplex₂.total.map ((G.mapHomologicalComplex (.up ℕ)).map f) (.up ℕ)

def edge (K : CochainComplex C ℕ) : K ⟶ FunctorResolutionTotal.total G K :=
  (AlgebraicGeometry.SheafCohomology.Cech.UpNatHorizontalEdge.HomologicalComplex₂.totalUpNatHorizontalEdge (ResolutionBicomplex.FunctorResolutionBicomplex.bicomplex G K)) K
    (ResolutionBicomplex.FunctorResolutionBicomplex.augmentation G η K)
    (fun q q' _ => ResolutionBicomplex.FunctorResolutionBicomplex.augmentation_comm G η K q q')
    (ResolutionBicomplex.FunctorResolutionBicomplex.augmentation_comp_d G η K)

omit [HasCoproducts.{0} C] [G.Additive] in
theorem augmentation_naturality {K L : CochainComplex C ℕ} (f : K ⟶ L) (q : ℕ) :
    (η.app (K.X q)).f 0 ≫ (G.map (f.f q)).f 0 = f.f q ≫ (η.app (L.X q)).f 0 := by
  have h := congrArg (fun a => a.f 0) (η.naturality (f.f q))
  exact h.symm.trans (congrArg (fun a => a ≫ (η.app (L.X q)).f 0)
    (CochainComplex.single₀_map_f_zero (f.f q)))

theorem naturality {K L : CochainComplex C ℕ} (f : K ⟶ L) :
    edge G η K ≫ FunctorResolutionTotal.map G f = f ≫ edge G η L := by
  ext q : 1
  change ((η.app (K.X q)).f 0 ≫ (ResolutionBicomplex.FunctorResolutionBicomplex.bicomplex G K).ιTotal
    (.up ℕ) q 0 q rfl) ≫
      (HomologicalComplex₂.total.map ((G.mapHomologicalComplex (.up ℕ)).map f) (.up ℕ)).f q =
    f.f q ≫ ((η.app (L.X q)).f 0 ≫
      (ResolutionBicomplex.FunctorResolutionBicomplex.bicomplex G L).ιTotal (.up ℕ) q 0 q rfl)
  exact (Category.assoc _ _ _).trans
    ((congrArg (fun a => (η.app (K.X q)).f 0 ≫ a)
      (HomologicalComplex₂.ιTotal_map (ResolutionBicomplex.FunctorResolutionBicomplex.bicomplex G K)
        (ResolutionBicomplex.FunctorResolutionBicomplex.bicomplex G L)
        ((G.mapHomologicalComplex (.up ℕ)).map f) (.up ℕ) q 0 q rfl)).trans
        ((Category.assoc _ _ _).symm.trans
          ((congrArg (fun a => a ≫ (ResolutionBicomplex.FunctorResolutionBicomplex.bicomplex G L).ιTotal
            (.up ℕ) q 0 q rfl) (augmentation_naturality G η f q)).trans (Category.assoc _ _ _))))

end

end OAI.NumberTheory.PadicHodge.GeometricComparison.Functor.ResolutionTotal.FunctorResolutionTotal

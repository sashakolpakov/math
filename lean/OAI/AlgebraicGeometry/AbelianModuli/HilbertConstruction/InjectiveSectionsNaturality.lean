import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.RestrictedSectionsNaturality
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Sheaf.CohomologyExcision

/-! # Injective Sections Naturality -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.InjectiveSectionsNaturality.IntrinsicCech

noncomputable section

/-! Natural cohomology comparisons for the actual chosen injective resolution,
including evaluation on any open subset. -/
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.TopologicalSpace
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
private def rebundleGroupHom {A B : AddCommGrpCat.{u}} (f : A ⟶ B) :
    AddCommGrpCat.of A ⟶ AddCommGrpCat.of B := AddCommGrpCat.ofHom f.hom

private def cohomologyMap {X : TopCat.{u}} {F G : TopCat.Sheaf AddCommGrpCat.{u} X}
    (f : F ⟶ G) (n : ℕ) :
    AddCommGrpCat.of ((CategoryTheory.Sheaf.functorH (Opens.grothendieckTopology X) n : _ ⥤ AddCommGrpCat.{u}).obj F) ⟶
      AddCommGrpCat.of ((CategoryTheory.Sheaf.functorH (Opens.grothendieckTopology X) n : _ ⥤ AddCommGrpCat.{u}).obj G) :=
  rebundleGroupHom ((CategoryTheory.Sheaf.functorH (Opens.grothendieckTopology X) n : _ ⥤ AddCommGrpCat.{u}).map f)

variable {X : TopCat.{u}}

def restrictedInjectiveCochain (F : TopCat.Sheaf AddCommGrpCat.{u} X) (V : Opens X) :
    CochainComplex (TopCat.Sheaf AddCommGrpCat.{u} (TopCat.of V)) ℕ :=
  ((TopologicalSheafRestriction.IntrinsicCech.restrict AddCommGrpCat.{u} V.isOpenEmbedding).mapHomologicalComplex (.up ℕ)).obj
    (injectiveResolution F).cocomplex

def restrictedInjectiveAug (F : TopCat.Sheaf AddCommGrpCat.{u} X) (V : Opens X) :
    (TopologicalSheafRestriction.IntrinsicCech.restrict AddCommGrpCat.{u} V.isOpenEmbedding).obj F ⟶ (restrictedInjectiveCochain F V).X 0 :=
  (TopologicalSheafRestriction.IntrinsicCech.restrict AddCommGrpCat.{u} V.isOpenEmbedding).map ((injectiveResolution F).ι.f 0)

instance restrictedInjectiveAug_mono (F : TopCat.Sheaf AddCommGrpCat.{u} X) (V : Opens X) :
    Mono (restrictedInjectiveAug F V) := by
  let I := injectiveResolution F
  have : Mono (I.ι.f 0) := inferInstance
  exact Functor.map_mono (TopologicalSheafRestriction.IntrinsicCech.restrict AddCommGrpCat.{u} V.isOpenEmbedding) (I.ι.f 0)

theorem restrictedInjectiveAug_zero (F : TopCat.Sheaf AddCommGrpCat.{u} X) (V : Opens X) :
    restrictedInjectiveAug F V ≫ (restrictedInjectiveCochain F V).d 0 1 = 0 := by
  let R := TopologicalSheafRestriction.IntrinsicCech.restrict AddCommGrpCat.{u} V.isOpenEmbedding
  change R.map ((injectiveResolution F).ι.f 0) ≫ R.map ((injectiveResolution F).cocomplex.d 0 1) = 0
  rw [← R.map_comp, (injectiveResolution F).ι_f_zero_comp_complex_d, R.map_zero]

theorem restrictedInjectiveAug_exact (F : TopCat.Sheaf AddCommGrpCat.{u} X) (V : Opens X) :
    (ShortComplex.mk (restrictedInjectiveAug F V) ((restrictedInjectiveCochain F V).d 0 1)
      (restrictedInjectiveAug_zero F V)).Exact :=
  (injectiveResolution F).exact₀.map (TopologicalSheafRestriction.IntrinsicCech.restrict AddCommGrpCat.{u} V.isOpenEmbedding)

theorem restrictedInjectiveCochain_exact (F : TopCat.Sheaf AddCommGrpCat.{u} X)
    (V : Opens X) (n : ℕ) : (AcyclicSheafResolution.IntrinsicCech.resolutionDifferentialShortComplex (restrictedInjectiveCochain F V) n).Exact :=
  ((injectiveResolution F).exact_succ n).map (TopologicalSheafRestriction.IntrinsicCech.restrict AddCommGrpCat.{u} V.isOpenEmbedding)

theorem restrictedInjectiveCochain_acyclic (F : TopCat.Sheaf AddCommGrpCat.{u} X)
    (V : Opens X) (p q : ℕ) :
    Subsingleton (CategoryTheory.Sheaf.H ((restrictedInjectiveCochain F V).X p) (q + 1)) := by
  have : TopCat.Sheaf.IsFlasque ((injectiveResolution F).cocomplex.X p) :=
    @TopologicalSheafCohomology.IntrinsicCech.injectiveSheaf_flasque X _ ((injectiveResolution F).injective p)
  have : TopCat.Sheaf.IsFlasque ((restrictedInjectiveCochain F V).X p) :=
    TopologicalSheafRestriction.IntrinsicCech.flasque_of_restrict _ ((injectiveResolution F).cocomplex.X p) V.isOpenEmbedding
  exact TopologicalSheafCohomology.IntrinsicCech.flasqueSheaf_positiveCohomology_subsingleton _ q

def naturalInjectiveOpenSectionsCohomologyIso
    (F : TopCat.Sheaf AddCommGrpCat.{u} X) (V : Opens X) (n : ℕ) :
    (InjectiveOpenSectionsCohomology.IntrinsicCech.injectiveOpenSectionsComplex F V).homology n ≅
      AddCommGrpCat.of ((CategoryTheory.Sheaf.functorH (Opens.grothendieckTopology V) n : _ ⥤ AddCommGrpCat.{u}).obj ((TopologicalSheafRestriction.IntrinsicCech.restrict AddCommGrpCat.{u} V.isOpenEmbedding).obj F)) :=
  HomologicalComplex.homologyMapIso
      (RestrictedSectionsNaturality.IntrinsicCech.restrictedTopSectionsComplexIso (injectiveResolution F).cocomplex V).symm n ≪≫
    AcyclicResolutionCohomology.IntrinsicCech.acyclicResolutionCohomologyIso (he := restrictedInjectiveAug_mono F V) (restrictedInjectiveCochain F V)
      (restrictedInjectiveAug F V) (restrictedInjectiveAug_zero F V)
      (restrictedInjectiveAug_exact F V) (restrictedInjectiveCochain_exact F V)
      (restrictedInjectiveCochain_acyclic F V) n

theorem naturalInjectiveOpenSectionsCohomologyIso_naturality
    {F G : TopCat.Sheaf AddCommGrpCat.{u} X} (f : F ⟶ G) (V : Opens X) (n : ℕ) :
    HomologicalComplex.homologyMap (RestrictedSectionsNaturality.IntrinsicCech.injectiveOpenSectionsMap f V) n ≫
        (naturalInjectiveOpenSectionsCohomologyIso G V n).hom =
      (naturalInjectiveOpenSectionsCohomologyIso F V n).hom ≫
        cohomologyMap ((TopologicalSheafRestriction.IntrinsicCech.restrict AddCommGrpCat.{u} V.isOpenEmbedding).map f) n := by
  let R := TopologicalSheafRestriction.IntrinsicCech.restrict AddCommGrpCat.{u} V.isOpenEmbedding
  let ψ := (R.mapHomologicalComplex (.up ℕ)).map (RestrictedSectionsNaturality.IntrinsicCech.chosenSheafResolutionMap f)
  have hψ : R.map f ≫ restrictedInjectiveAug G V = restrictedInjectiveAug F V ≫ ψ.f 0 := by
    change R.map f ≫ R.map ((injectiveResolution G).ι.f 0) =
      R.map ((injectiveResolution F).ι.f 0) ≫ R.map ((RestrictedSectionsNaturality.IntrinsicCech.chosenSheafResolutionMap f).f 0)
    rw [← R.map_comp, ← R.map_comp, RestrictedSectionsNaturality.IntrinsicCech.chosenSheafResolutionMap_aug]
  have hc := congrArg (fun φ => HomologicalComplex.homologyMap φ n)
    (RestrictedSectionsNaturality.IntrinsicCech.restrictedTopSectionsComplexIso_naturality (RestrictedSectionsNaturality.IntrinsicCech.chosenSheafResolutionMap f) V)
  simp only [HomologicalComplex.homologyMap_comp] at hc
  have ha := AcyclicResolutionNaturality.IntrinsicCech.acyclicResolutionCohomologyIso_naturality
    (restrictedInjectiveAug F V) (restrictedInjectiveAug_zero F V)
    (restrictedInjectiveAug G V) (restrictedInjectiveAug_zero G V)
    (restrictedInjectiveAug_exact F V) (restrictedInjectiveAug_exact G V)
    (restrictedInjectiveCochain_exact F V) (restrictedInjectiveCochain_exact G V)
    (restrictedInjectiveCochain_acyclic F V) (restrictedInjectiveCochain_acyclic G V)
    (R.map f) ψ hψ n
  dsimp only [naturalInjectiveOpenSectionsCohomologyIso, Iso.trans_hom,
    HomologicalComplex.homologyMapIso, Iso.symm_hom]
  erw [← Category.assoc, hc, Category.assoc, ha, ← Category.assoc]

theorem injectiveGlobalSectionsCohomologyIso_naturality
    {F G : TopCat.Sheaf AddCommGrpCat.{u} X} (f : F ⟶ G) (n : ℕ) :
    HomologicalComplex.homologyMap (RestrictedSectionsNaturality.IntrinsicCech.injectiveOpenSectionsMap f ⊤) n ≫
        (HilbertConstruction.Sheaf.CohomologyExcision.IntrinsicCech.injectiveGlobalSectionsCohomologyIso G n).hom =
      (HilbertConstruction.Sheaf.CohomologyExcision.IntrinsicCech.injectiveGlobalSectionsCohomologyIso F n).hom ≫
        cohomologyMap f n := by
  have hF (p q : ℕ) : Subsingleton
      (CategoryTheory.Sheaf.H ((injectiveResolution F).cocomplex.X p) (q + 1)) := by
    have : TopCat.Sheaf.IsFlasque ((injectiveResolution F).cocomplex.X p) :=
      @TopologicalSheafCohomology.IntrinsicCech.injectiveSheaf_flasque X _ ((injectiveResolution F).injective p)
    exact TopologicalSheafCohomology.IntrinsicCech.flasqueSheaf_positiveCohomology_subsingleton _ q
  have hG (p q : ℕ) : Subsingleton
      (CategoryTheory.Sheaf.H ((injectiveResolution G).cocomplex.X p) (q + 1)) := by
    have : TopCat.Sheaf.IsFlasque ((injectiveResolution G).cocomplex.X p) :=
      @TopologicalSheafCohomology.IntrinsicCech.injectiveSheaf_flasque X _ ((injectiveResolution G).injective p)
    exact TopologicalSheafCohomology.IntrinsicCech.flasqueSheaf_positiveCohomology_subsingleton _ q
  exact AcyclicResolutionNaturality.IntrinsicCech.acyclicResolutionCohomologyIso_naturality
    ((injectiveResolution F).ι.f 0) (injectiveResolution F).ι_f_zero_comp_complex_d
    ((injectiveResolution G).ι.f 0) (injectiveResolution G).ι_f_zero_comp_complex_d
    (injectiveResolution F).exact₀ (injectiveResolution G).exact₀
    (fun q => (injectiveResolution F).exact_succ q) (fun q => (injectiveResolution G).exact_succ q)
    hF hG f (RestrictedSectionsNaturality.IntrinsicCech.chosenSheafResolutionMap f) (RestrictedSectionsNaturality.IntrinsicCech.chosenSheafResolutionMap_aug f) n

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.InjectiveSectionsNaturality.IntrinsicCech

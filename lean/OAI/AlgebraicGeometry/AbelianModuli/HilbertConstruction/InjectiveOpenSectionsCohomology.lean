import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.AcyclicResolutionCohomology
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.TopologicalSheafRestriction

/-! # Injective Open Sections Cohomology -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.InjectiveOpenSectionsCohomology.IntrinsicCech

noncomputable section

/-! Evaluating the actual chosen injective resolution on an open subset computes the actual cohomology of the restricted sheaf. Restriction preserves exactness, and the restricted injective terms are flasque. -/
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.TopologicalSpace Opposite
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {X : TopCat.{u}}

def sheafOpenEvaluation (X : TopCat.{u}) (V : Opens X) :
    TopCat.Sheaf AddCommGrpCat.{u} X ⥤ AddCommGrpCat.{u} :=
  sheafToPresheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u} ⋙
    (evaluation (Opens X)ᵒᵖ AddCommGrpCat.{u}).obj (op V)

instance sheafOpenEvaluation_additive (V : Opens X) : (sheafOpenEvaluation X V).Additive where
  map_add := by intros; rfl

def injectiveOpenSectionsComplex (F : TopCat.Sheaf AddCommGrpCat.{u} X) (V : Opens X) :
    CochainComplex AddCommGrpCat.{u} ℕ :=
  ((sheafOpenEvaluation X V).mapHomologicalComplex (.up ℕ)).obj (injectiveResolution F).cocomplex

def injectiveOpenSectionsCohomologyIso
    (F : TopCat.Sheaf AddCommGrpCat.{u} X) (V : Opens X) (n : ℕ) :
    (injectiveOpenSectionsComplex F V).homology n ≅
      AddCommGrpCat.of (((CategoryTheory.Sheaf.functorH (Opens.grothendieckTopology V) n :
        _ ⥤ AddCommGrpCat.{u}).obj ((TopologicalSheafRestriction.IntrinsicCech.restrict AddCommGrpCat V.isOpenEmbedding).obj F))) := by
  let I := injectiveResolution F
  let R := TopologicalSheafRestriction.IntrinsicCech.restrict AddCommGrpCat.{u} V.isOpenEmbedding
  have : PreservesFiniteColimits R := inferInstance
  let K := (R.mapHomologicalComplex (.up ℕ)).obj I.cocomplex
  let e : R.obj F ⟶ K.X 0 := R.map (I.ι.f 0)
  have w : e ≫ K.d 0 1 = 0 := by
    change R.map (I.ι.f 0) ≫ R.map (I.cocomplex.d 0 1) = 0
    rw [← R.map_comp, I.ι_f_zero_comp_complex_d, R.map_zero]
  have : Mono e := Functor.map_mono R (I.ι.f 0)
  have haug : (ShortComplex.mk e (K.d 0 1) w).Exact := I.exact₀.map R
  have hpos : ∀ q, (AcyclicSheafResolution.IntrinsicCech.resolutionDifferentialShortComplex K q).Exact :=
    fun q => (I.exact_succ q).map R
  have hK (p q : ℕ) : Subsingleton (CategoryTheory.Sheaf.H (K.X p) (q + 1)) := by
    have : TopCat.Sheaf.IsFlasque (I.cocomplex.X p) :=
      @TopologicalSheafCohomology.IntrinsicCech.injectiveSheaf_flasque X (I.cocomplex.X p) (I.injective p)
    have : TopCat.Sheaf.IsFlasque (K.X p) :=
      TopologicalSheafRestriction.IntrinsicCech.flasque_of_restrict _ (I.cocomplex.X p) V.isOpenEmbedding
    exact TopologicalSheafCohomology.IntrinsicCech.flasqueSheaf_positiveCohomology_subsingleton (K.X p) q
  let eC : AcyclicResolutionCohomology.IntrinsicCech.sheafTopSectionsComplex K ≅ injectiveOpenSectionsComplex F V := by
    change ((sheafOpenEvaluation X (V.isOpenEmbedding.functor.obj ⊤)).mapHomologicalComplex (.up ℕ)).obj
        I.cocomplex ≅ injectiveOpenSectionsComplex F V
    rw [Opens.isOpenEmbedding_obj_top V]
    exact Iso.refl _
  exact HomologicalComplex.homologyMapIso eC.symm n ≪≫
    AcyclicResolutionCohomology.IntrinsicCech.acyclicResolutionCohomologyIso K e w haug hpos hK n

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.InjectiveOpenSectionsCohomology.IntrinsicCech

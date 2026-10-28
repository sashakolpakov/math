import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.InjectiveTwoOpenComplex

/-! # Cohomology Excision -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Sheaf.CohomologyExcision.IntrinsicCech

noncomputable section

/-! If a second open and its overlap with a first open have zero cohomology in every degree, the actual cohomology of their union equals that of the first open. -/
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.TopologicalSpace
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {X : TopCat.{u}}

def injectiveGlobalSectionsCohomologyIso (F : TopCat.Sheaf AddCommGrpCat.{u} X) (n : ℕ) :
    (InjectiveOpenSectionsCohomology.IntrinsicCech.injectiveOpenSectionsComplex F ⊤).homology n ≅ AddCommGrpCat.of ((CategoryTheory.Sheaf.functorH (Opens.grothendieckTopology X) n : _ ⥤ AddCommGrpCat.{u}).obj F) := by
  let I := injectiveResolution F
  have hI (p q : ℕ) : Subsingleton (CategoryTheory.Sheaf.H (I.cocomplex.X p) (q + 1)) := by
    have : TopCat.Sheaf.IsFlasque (I.cocomplex.X p) :=
      @TopologicalSheafCohomology.IntrinsicCech.injectiveSheaf_flasque X (I.cocomplex.X p) (I.injective p)
    exact TopologicalSheafCohomology.IntrinsicCech.flasqueSheaf_positiveCohomology_subsingleton (I.cocomplex.X p) q
  exact AcyclicResolutionCohomology.IntrinsicCech.acyclicResolutionCohomologyIso I.cocomplex (I.ι.f 0) I.ι_f_zero_comp_complex_d
    I.exact₀ (fun q => I.exact_succ q) hI n

def sheafCohomologyTwoOpenExcisionIso
    (F : TopCat.Sheaf AddCommGrpCat.{u} X) (U V : Opens X) (hcover : U ⊔ V = ⊤)
    (hV : ∀ q, Subsingleton (CategoryTheory.Sheaf.H ((TopologicalSheafRestriction.IntrinsicCech.restrict AddCommGrpCat V.isOpenEmbedding).obj F) q))
    (hUV : ∀ q, Subsingleton (CategoryTheory.Sheaf.H
      ((TopologicalSheafRestriction.IntrinsicCech.restrict AddCommGrpCat (U ⊓ V).isOpenEmbedding).obj F) q)) (n : ℕ) :
    AddCommGrpCat.of ((CategoryTheory.Sheaf.functorH (Opens.grothendieckTopology X) n : _ ⥤ AddCommGrpCat.{u}).obj F) ≅
      AddCommGrpCat.of ((CategoryTheory.Sheaf.functorH (Opens.grothendieckTopology U) n : _ ⥤ AddCommGrpCat.{u}).obj ((TopologicalSheafRestriction.IntrinsicCech.restrict AddCommGrpCat U.isOpenEmbedding).obj F)) := by
  let f := InjectiveTwoOpenComplex.IntrinsicCech.injectiveOpenSectionsRestriction F (show U ≤ U ⊔ V from le_sup_left)
  have : QuasiIso f := InjectiveTwoOpenComplex.IntrinsicCech.injectiveOpenSectionsRestriction_quasiIso F U V hV hUV
  let e : InjectiveOpenSectionsCohomology.IntrinsicCech.injectiveOpenSectionsComplex F (U ⊔ V) ≅ InjectiveOpenSectionsCohomology.IntrinsicCech.injectiveOpenSectionsComplex F ⊤ :=
    eqToIso (congrArg (InjectiveOpenSectionsCohomology.IntrinsicCech.injectiveOpenSectionsComplex F) hcover)
  exact (injectiveGlobalSectionsCohomologyIso F n).symm ≪≫
    HomologicalComplex.homologyMapIso e.symm n ≪≫
    asIso (HomologicalComplex.homologyMap f n) ≪≫ InjectiveOpenSectionsCohomology.IntrinsicCech.injectiveOpenSectionsCohomologyIso F U n

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Sheaf.CohomologyExcision.IntrinsicCech

import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.InjectiveOpenSectionsCohomology
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Sheaf.TwoOpenSections
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Additive.CochainProducts

/-! # Injective Two Open Complex -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.InjectiveTwoOpenComplex.IntrinsicCech

noncomputable section

/-! The section sequence on two opens gives a short exact sequence of actual injective-resolution section complexes. If the second open and overlap have zero cohomology, restriction to the first open is a quasi-isomorphism. -/
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.TopologicalSpace Opposite
universe u
variable {X : TopCat.{u}} (F : TopCat.Sheaf AddCommGrpCat.{u} X)

def injectiveOpenSectionsRestriction {U V : Opens X} (h : U ≤ V) :
    InjectiveOpenSectionsCohomology.IntrinsicCech.injectiveOpenSectionsComplex F V ⟶ InjectiveOpenSectionsCohomology.IntrinsicCech.injectiveOpenSectionsComplex F U where
  f n := ((injectiveResolution F).cocomplex.X n).obj.map (homOfLE h).op
  comm' i j _hij := ((injectiveResolution F).cocomplex.d i j).hom.naturality (homOfLE h).op

variable (U V : Opens X)

def injectiveTwoOpenRestriction : InjectiveOpenSectionsCohomology.IntrinsicCech.injectiveOpenSectionsComplex F (U ⊔ V) ⟶
    Additive.CochainProducts.additiveCochainProduct (InjectiveOpenSectionsCohomology.IntrinsicCech.injectiveOpenSectionsComplex F U) (InjectiveOpenSectionsCohomology.IntrinsicCech.injectiveOpenSectionsComplex F V) where
  f n := AddCommGrpCat.ofHom (HilbertConstruction.Sheaf.TwoOpenSections.IntrinsicCech.twoOpenSectionsRestriction ((injectiveResolution F).cocomplex.X n) U V)
  comm' i j _hij := by
    ext x
    exact (HilbertConstruction.Sheaf.TwoOpenSections.IntrinsicCech.twoOpenSectionsRestriction_naturality ((injectiveResolution F).cocomplex.X i) U V
      ((injectiveResolution F).cocomplex.d i j) x).symm

def injectiveTwoOpenDifference :
    Additive.CochainProducts.additiveCochainProduct (InjectiveOpenSectionsCohomology.IntrinsicCech.injectiveOpenSectionsComplex F U) (InjectiveOpenSectionsCohomology.IntrinsicCech.injectiveOpenSectionsComplex F V) ⟶
      InjectiveOpenSectionsCohomology.IntrinsicCech.injectiveOpenSectionsComplex F (U ⊓ V) where
  f n := AddCommGrpCat.ofHom (HilbertConstruction.Sheaf.TwoOpenSections.IntrinsicCech.twoOpenSectionsDifference ((injectiveResolution F).cocomplex.X n) U V)
  comm' i j _hij := by
    ext x
    exact HilbertConstruction.Sheaf.TwoOpenSections.IntrinsicCech.twoOpenSectionsDifference_naturality ((injectiveResolution F).cocomplex.X i) U V
      ((injectiveResolution F).cocomplex.d i j) x

def injectiveTwoOpenShortComplex : ShortComplex (CochainComplex AddCommGrpCat.{u} ℕ) :=
  ShortComplex.mk (injectiveTwoOpenRestriction F U V) (injectiveTwoOpenDifference F U V) (by
    ext n x
    exact HilbertConstruction.Sheaf.TwoOpenSections.IntrinsicCech.twoOpenSections_comp ((injectiveResolution F).cocomplex.X n) U V x)

theorem injectiveTwoOpen_shortExact : (injectiveTwoOpenShortComplex F U V).ShortExact := by
  apply HomologicalComplex.shortExact_of_degreewise_shortExact
  intro n
  have : TopCat.Sheaf.IsFlasque ((injectiveResolution F).cocomplex.X n) :=
    @TopologicalSheafCohomology.IntrinsicCech.injectiveSheaf_flasque X ((injectiveResolution F).cocomplex.X n) ((injectiveResolution F).injective n)
  exact HilbertConstruction.Sheaf.TwoOpenSections.IntrinsicCech.twoOpenSections_shortExact ((injectiveResolution F).cocomplex.X n) U V

theorem injectiveOpenSections_acyclic_of_cohomology_zero (W : Opens X)
    (hW : ∀ q, Subsingleton (CategoryTheory.Sheaf.H ((TopologicalSheafRestriction.IntrinsicCech.restrict AddCommGrpCat W.isOpenEmbedding).obj F) q)) :
    (InjectiveOpenSectionsCohomology.IntrinsicCech.injectiveOpenSectionsComplex F W).Acyclic := by
  intro q
  rw [HomologicalComplex.exactAt_iff_isZero_homology]
  let e := InjectiveOpenSectionsCohomology.IntrinsicCech.injectiveOpenSectionsCohomologyIso F W q
  have hi : Function.Injective e.hom := (AddCommGrpCat.mono_iff_injective e.hom).mp inferInstance
  exact AddCommGrpCat.isZero_iff_subsingleton.mpr ⟨fun x y => hi ((hW q).elim _ _)⟩

theorem injectiveOpenSectionsRestriction_quasiIso
    (hV : ∀ q, Subsingleton (CategoryTheory.Sheaf.H ((TopologicalSheafRestriction.IntrinsicCech.restrict AddCommGrpCat V.isOpenEmbedding).obj F) q))
    (hUV : ∀ q, Subsingleton (CategoryTheory.Sheaf.H
      ((TopologicalSheafRestriction.IntrinsicCech.restrict AddCommGrpCat (U ⊓ V).isOpenEmbedding).obj F) q)) :
    QuasiIso (injectiveOpenSectionsRestriction F (show U ≤ U ⊔ V from le_sup_left)) := by
  have : QuasiIso (injectiveTwoOpenRestriction F U V) :=
    Cochain.AcyclicSideComparison.cochain_quasiIso_f_of_acyclic_last (injectiveTwoOpen_shortExact F U V)
      (injectiveOpenSections_acyclic_of_cohomology_zero F (U ⊓ V) hUV)
  have : QuasiIso (Additive.CochainProducts.additiveCochainProductFst (InjectiveOpenSectionsCohomology.IntrinsicCech.injectiveOpenSectionsComplex F U)
      (InjectiveOpenSectionsCohomology.IntrinsicCech.injectiveOpenSectionsComplex F V)) :=
    Additive.CochainProducts.additiveCochainProductFst_quasiIso _ _ (injectiveOpenSections_acyclic_of_cohomology_zero F V hV)
  have h : injectiveTwoOpenRestriction F U V ≫
      Additive.CochainProducts.additiveCochainProductFst (InjectiveOpenSectionsCohomology.IntrinsicCech.injectiveOpenSectionsComplex F U) (InjectiveOpenSectionsCohomology.IntrinsicCech.injectiveOpenSectionsComplex F V) =
      injectiveOpenSectionsRestriction F (show U ≤ U ⊔ V from le_sup_left) := by
    ext n x
    rfl
  rw [← h]
  exact quasiIso_comp _ _

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.InjectiveTwoOpenComplex.IntrinsicCech

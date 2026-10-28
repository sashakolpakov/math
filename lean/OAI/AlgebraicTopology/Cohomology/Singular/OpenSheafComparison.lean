import OAI.AlgebraicTopology.Cohomology.Singular.OpenCochainPresheafComparison
import OAI.AlgebraicTopology.Cohomology.Singular.ParacompactComparison
import Mathlib.CategoryTheory.Sites.CoverLifting
import Mathlib.Topology.Sheaves.Over

/-! # Open Sheaf Comparison -/

namespace OAI.AlgebraicTopology.Cohomology.Singular.OpenSheafComparison

noncomputable section

/-!
# Singular-cochain sheafification on actual open subspaces

The open-image functor is both continuous and cocontinuous for the genuine
topological sites. Sheafification therefore commutes with restriction to
an open subspace, including its canonical unit. The natural identification
of singular cochains on nested open subspaces then gives the actual
comparison on all open sections, respecting the cochain differential.
-/

open _root_.CategoryTheory _root_.CategoryTheory.Limits Opposite _root_.TopologicalSpace

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {R : Type} [Ring R]
variable (X : TopCat.{0}) (U : Opens X)

/-- The actual image functor for an open inclusion is continuous as a
functor of the ordinary topological sites. -/
instance nestedOpenImageFunctor_isContinuous :
    (OpenCochainPresheafComparison.nestedOpenImageFunctor U).IsContinuous (Opens.grothendieckTopology U)
      (Opens.grothendieckTopology X) :=
  U.isOpenEmbedding.functor_isContinuous

/-- The same image functor lifts covering sieves, by its adjunction with
inverse image and the cover-preserving property of inverse image. -/
instance nestedOpenImageFunctor_isCocontinuous :
    (OpenCochainPresheafComparison.nestedOpenImageFunctor U).IsCocontinuous (Opens.grothendieckTopology U)
      (Opens.grothendieckTopology X) := by
  exact (U.isOpenEmbedding.isOpenMap.adjunction.isCocontinuous_iff_coverPreserving
    (Opens.grothendieckTopology U) (Opens.grothendieckTopology X)).2
      (coverPreserving_opens_map U.inclusion')

/-- Sheafification commutes with genuine restriction to an open subspace.
This is the canonical compatibility of the actual site functors. -/
def openSheafificationNaturalIso :
    (Functor.whiskeringLeft _ _ (ModuleCat.{0} R)).obj (OpenCochainPresheafComparison.nestedOpenImageFunctor U).op ⋙
        presheafToSheaf (Opens.grothendieckTopology U) (ModuleCat.{0} R) ≅
      presheafToSheaf (Opens.grothendieckTopology X) (ModuleCat.{0} R) ⋙
        U.sheafRestrict :=
  (OpenCochainPresheafComparison.nestedOpenImageFunctor U).pushforwardContinuousSheafificationCompatibility
    (ModuleCat.{0} R) (Opens.grothendieckTopology U) (Opens.grothendieckTopology X)

/-- The canonical open-restriction comparison for one module presheaf. -/
def openSheafificationIso (P : X.Presheaf (ModuleCat.{0} R)) :
    (presheafToSheaf (Opens.grothendieckTopology U) (ModuleCat.{0} R)).obj
        ((OpenCochainPresheafComparison.nestedOpenImageFunctor U).op ⋙ P) ≅
      U.sheafRestrict.obj
        ((presheafToSheaf (Opens.grothendieckTopology X) (ModuleCat.{0} R)).obj P) :=
  (openSheafificationNaturalIso (R := R) X U).app P

/-- The compatibility isomorphism preserves the actual sheafification unit. -/
theorem openSheafificationIso_unit (P : X.Presheaf (ModuleCat.{0} R)) :
    CategoryTheory.toSheafify (Opens.grothendieckTopology U)
        ((OpenCochainPresheafComparison.nestedOpenImageFunctor U).op ⋙ P) ≫
        (openSheafificationIso X U P).hom.hom =
      Functor.whiskerLeft (OpenCochainPresheafComparison.nestedOpenImageFunctor U).op
        (CategoryTheory.toSheafify (Opens.grothendieckTopology X) P) :=
  (OpenCochainPresheafComparison.nestedOpenImageFunctor U).toSheafify_pullbackSheafificationCompatibility
    (ModuleCat.{0} R) (Opens.grothendieckTopology U) (Opens.grothendieckTopology X) P

/-- The inverse open-sheafification comparison also preserves the unit. -/
theorem openSheafificationIso_unit_inv (P : X.Presheaf (ModuleCat.{0} R)) :
    Functor.whiskerLeft (OpenCochainPresheafComparison.nestedOpenImageFunctor U).op
        (CategoryTheory.toSheafify (Opens.grothendieckTopology X) P) ≫
        (openSheafificationIso X U P).inv.hom =
      CategoryTheory.toSheafify (Opens.grothendieckTopology U)
        ((OpenCochainPresheafComparison.nestedOpenImageFunctor U).op ⋙ P) := by
  rw [← openSheafificationIso_unit]
  let e := (sheafToPresheaf (Opens.grothendieckTopology U) (ModuleCat.{0} R)).mapIso
    (openSheafificationIso X U P)
  change (_ ≫ e.hom) ≫ e.inv = _
  rw [Category.assoc, e.hom_inv_id, Category.comp_id]

/-- Restriction commutes with sheafification for actual cochain complexes,
so the comparison also preserves every differential. -/
def openSheafificationComplexIso
    (K : CochainComplex (X.Presheaf (ModuleCat.{0} R)) ℕ) :
    SheafQuasiIso.sheafifiedCochainComplex (X := TopCat.of U) ((OpenCochainPresheafComparison.nestedOpenPresheafComplexFunctor U).obj K) ≅
      ((U.sheafRestrict (C := ModuleCat.{0} R)).mapHomologicalComplex
        (ComplexShape.up ℕ)).obj (SheafQuasiIso.sheafifiedCochainComplex K) :=
  (NatIso.mapHomologicalComplex (openSheafificationNaturalIso (R := R) X U)
    (ComplexShape.up ℕ)).app K

@[simp]
theorem openSheafificationComplexIso_hom_f
    (K : CochainComplex (X.Presheaf (ModuleCat.{0} R)) ℕ) (n : ℕ) :
    (openSheafificationComplexIso X U K).hom.f n =
      (openSheafificationIso X U (K.X n)).hom := rfl

/-- The restricted ambient singular sheaf complex is canonically the
singular sheaf complex of the actual open subspace. -/
def singularOpenSheafComplexIso (M : ModuleCat.{0} R) (X : TopCat.{0}) (U : Opens X) :
    ((U.sheafRestrict (C := ModuleCat.{0} R)).mapHomologicalComplex
      (ComplexShape.up ℕ)).obj
        (SheafQuasiIso.sheafifiedCochainComplex (DeRham.Comparison.SingularPresheaf.singularPresheafComplex M X)) ≅
      SheafQuasiIso.sheafifiedCochainComplex (DeRham.Comparison.SingularPresheaf.singularPresheafComplex M (TopCat.of U)) :=
  (openSheafificationComplexIso X U (DeRham.Comparison.SingularPresheaf.singularPresheafComplex M X)).symm ≪≫
    ((presheafToSheaf (Opens.grothendieckTopology U) (ModuleCat.{0} R)).mapHomologicalComplex
      (ComplexShape.up ℕ)).mapIso (OpenCochainPresheafComparison.singularOpenPresheafComplexIso M U)

/-- Evaluation of the underlying presheaf of a module sheaf on an actual open set. -/
def sheafSectionsFunctor : TopCat.Sheaf (ModuleCat.{0} R) X ⥤ ModuleCat.{0} R :=
  sheafToPresheaf (Opens.grothendieckTopology X) (ModuleCat.{0} R) ⋙
    (evaluation (Opens X)ᵒᵖ (ModuleCat.{0} R)).obj (op U)

instance sheafSectionsFunctor_additive :
    (sheafSectionsFunctor (R := R) X U).Additive := by
  constructor
  intro F G f g
  rfl

instance sheafSectionsFunctor_preservesZeroMorphisms :
    (sheafSectionsFunctor (R := R) X U).PreservesZeroMorphisms := by
  constructor
  intro F G
  rfl

/-- The image of the top open subset of an open subspace is that same
ambient open subset; both arrows are literal inclusions. -/
def nestedOpenTopIso : ChartOpenDiffeomorph.nestedOpenImage U ⊤ ≅ U where
  hom := homOfLE (ChartOpenDiffeomorph.nestedOpenImage_subset U ⊤)
  inv := homOfLE (fun x hx => ⟨⟨x, hx⟩, by trivial, rfl⟩)
  hom_inv_id := Subsingleton.elim _ _
  inv_hom_id := Subsingleton.elim _ _

/-- Ambient sections on U are the top sections of the actual sheaf
restriction to U, naturally in the sheaf. -/
def openSheafSectionsNaturalIso :
    sheafSectionsFunctor (R := R) X U ≅
      U.sheafRestrict ⋙ sheafSectionsFunctor (R := R) (TopCat.of U) ⊤ :=
  NatIso.ofComponents (fun F => F.obj.mapIso (nestedOpenTopIso X U).op)
    (fun f => (f.hom.naturality (nestedOpenTopIso X U).hom.op).symm)

/-- Sections on an open set of the genuine ambient singular sheaf complex. -/
def singularSheafSections (M : ModuleCat.{0} R) (X : TopCat.{0}) (U : Opens X) :
    CochainComplex (ModuleCat.{0} R) ℕ :=
  ((sheafSectionsFunctor (R := R) X U).mapHomologicalComplex (ComplexShape.up ℕ)).obj
    (SheafQuasiIso.sheafifiedCochainComplex (DeRham.Comparison.SingularPresheaf.singularPresheafComplex M X))

@[simp]
theorem singularSheafSections_top (M : ModuleCat.{0} R) (X : TopCat.{0}) :
    singularSheafSections M X ⊤ = LocallyZeroCochains.singularSheafGlobalSections M X := rfl

/-- The actual restriction of ambient singular-sheaf sections. -/
def singularSheafSectionsRestriction (M : ModuleCat.{0} R) (X : TopCat.{0})
    {V W : Opens X} (i : V ⟶ W) :
    singularSheafSections M X W ⟶ singularSheafSections M X V where
  f n := ((SheafQuasiIso.sheafifiedCochainComplex (DeRham.Comparison.SingularPresheaf.singularPresheafComplex M X)).X n).obj.map i.op
  comm' p q _ :=
    ((SheafQuasiIso.sheafifiedCochainComplex (DeRham.Comparison.SingularPresheaf.singularPresheafComplex M X)).d p q).hom.naturality i.op

/-- The actual sheafification unit on an open set, with its source the
genuine singular cochains of that open subspace. -/
def singularCochainsToOpenSheafSections (M : ModuleCat.{0} R) (X : TopCat.{0}) (U : Opens X) :
    Basic.singularCochains M (TopCat.of U) ⟶ singularSheafSections M X U where
  f n := (CategoryTheory.toSheafify (Opens.grothendieckTopology X)
    (DeRham.Comparison.SingularPresheaf.singularCochainDegreePresheaf M X n)).app (op U)
  comm' p q _ := by
    exact (congrArg (fun f => f.app (op U))
      (CategoryTheory.toSheafify_naturality (Opens.grothendieckTopology X)
        ((DeRham.Comparison.SingularPresheaf.singularPresheafComplex M X).d p q))).symm

@[simp]
theorem singularCochainsToOpenSheafSections_f (M : ModuleCat.{0} R)
    (X : TopCat.{0}) (U : Opens X) (n : ℕ) :
    (singularCochainsToOpenSheafSections M X U).f n =
      (CategoryTheory.toSheafify (Opens.grothendieckTopology X)
        (DeRham.Comparison.SingularPresheaf.singularCochainDegreePresheaf M X n)).app (op U) := rfl

/-- The actual open-section comparison commutes with every open inclusion. -/
theorem singularCochainsToOpenSheafSections_naturality (M : ModuleCat.{0} R) (X : TopCat.{0})
    {V W : Opens X} (i : V ⟶ W) :
    Singular.Functor.singularPullback M ((Opens.toTopCat X).map i) ≫
        singularCochainsToOpenSheafSections M X V =
      singularCochainsToOpenSheafSections M X W ≫
        singularSheafSectionsRestriction M X i := by
  apply HomologicalComplex.Hom.ext
  funext n
  exact (CategoryTheory.toSheafify (Opens.grothendieckTopology X)
    (DeRham.Comparison.SingularPresheaf.singularCochainDegreePresheaf M X n)).naturality i.op

/-- The installed global comparison restricts to the canonical comparison
on every actual open subspace. -/
theorem singularCochainsToOpenSheafSections_global (M : ModuleCat.{0} R)
    (X : TopCat.{0}) (U : Opens X) :
    Singular.Functor.singularPullback M (Opens.inclusion' U) ≫ singularCochainsToOpenSheafSections M X U =
      LocallyZeroCochains.singularCochainsToSheafSections M X ≫
        singularSheafSectionsRestriction M X (homOfLE (show U ≤ ⊤ from le_top)) := by
  change _ = (Singular.Functor.singularPullback M (Opens.inclusion' (⊤ : Opens X)) ≫
    singularCochainsToOpenSheafSections M X ⊤) ≫ _
  rw [Category.assoc, ← singularCochainsToOpenSheafSections_naturality,
    ← Category.assoc, ← Singular.Functor.singularPullback_comp]
  rfl

/-- Ambient open sections of the singular sheaf complex are canonically
the global sections of the intrinsic singular sheaf complex on that open. -/
def singularSheafOpenSectionsIso (M : ModuleCat.{0} R) (X : TopCat.{0}) (U : Opens X) :
    singularSheafSections M X U ≅ LocallyZeroCochains.singularSheafGlobalSections M (TopCat.of U) := by
  letI : (U.sheafRestrict ⋙ sheafSectionsFunctor (R := R) (TopCat.of U) ⊤).PreservesZeroMorphisms :=
    ⟨fun _ _ => rfl⟩
  exact (NatIso.mapHomologicalComplex (openSheafSectionsNaturalIso (R := R) X U)
    (ComplexShape.up ℕ)).app (SheafQuasiIso.sheafifiedCochainComplex (DeRham.Comparison.SingularPresheaf.singularPresheafComplex M X)) ≪≫
      ((sheafSectionsFunctor (R := R) (TopCat.of U) ⊤).mapHomologicalComplex
        (ComplexShape.up ℕ)).mapIso (singularOpenSheafComplexIso M X U)

/-- The section comparison is given degreewise by the canonical open
image identification and the actual sheafification comparison. -/
theorem singularSheafOpenSectionsIso_hom_f (M : ModuleCat.{0} R)
    (X : TopCat.{0}) (U : Opens X) (n : ℕ) :
    (singularSheafOpenSectionsIso M X U).hom.f n =
      (CategoryTheory.sheafify (Opens.grothendieckTopology X)
        (DeRham.Comparison.SingularPresheaf.singularCochainDegreePresheaf M X n)).map (nestedOpenTopIso X U).hom.op ≫
        ((openSheafificationIso X U (DeRham.Comparison.SingularPresheaf.singularCochainDegreePresheaf M X n)).inv.hom.app (op ⊤) ≫
          (CategoryTheory.sheafifyMap (Opens.grothendieckTopology U)
            ((OpenCochainPresheafComparison.singularOpenPresheafComplexIso M U).hom.f n)).app (op ⊤)) := rfl

/-- On actual cochains the two top-open identifications compose to the
ordinary pullback along the inclusion of the top open subset of U. -/
theorem singularOpenTopPullback (M : ModuleCat.{0} R)
    (X : TopCat.{0}) (U : Opens X) (n : ℕ) :
    (DeRham.Comparison.SingularPresheaf.singularCochainDegreePresheaf M X n).map (nestedOpenTopIso X U).hom.op ≫
        ((OpenCochainPresheafComparison.singularOpenPresheafComplexIso M U).hom.f n).app (op ⊤) =
      (Singular.Functor.singularPullback M (Opens.inclusion' (⊤ : Opens (TopCat.of U)))).f n := by
  have h : Singular.Functor.singularPullback M ((Opens.toTopCat X).map (nestedOpenTopIso X U).hom) ≫
      (OpenCochainPresheafComparison.singularOpenCochainPresheafIso M U).hom.app (op ⊤) =
        Singular.Functor.singularPullback M (Opens.inclusion' (⊤ : Opens (TopCat.of U))) := by
    rw [OpenCochainPresheafComparison.singularOpenCochainPresheafIso_hom_app, ← Singular.Functor.singularPullback_comp]
    rfl
  exact congrArg (fun f => f.f n) h

/-- The canonical open-section isomorphism carries the actual ambient
sheafification unit to the installed intrinsic global comparison. -/
theorem singularSheafOpenSectionsIso_unit (M : ModuleCat.{0} R)
    (X : TopCat.{0}) (U : Opens X) :
    singularCochainsToOpenSheafSections M X U ≫ (singularSheafOpenSectionsIso M X U).hom =
      LocallyZeroCochains.singularCochainsToSheafSections M (TopCat.of U) := by
  apply HomologicalComplex.Hom.ext
  funext n
  rw [HomologicalComplex.comp_f, singularCochainsToOpenSheafSections_f,
    singularSheafOpenSectionsIso_hom_f, LocallyZeroCochains.singularCochainsToSheafSections_f]
  let P := DeRham.Comparison.SingularPresheaf.singularCochainDegreePresheaf M X n
  let Q := (OpenCochainPresheafComparison.nestedOpenImageFunctor U).op ⋙ P
  let T := DeRham.Comparison.SingularPresheaf.singularCochainDegreePresheaf M (TopCat.of U) n
  let α : Q ⟶ T := (OpenCochainPresheafComparison.singularOpenPresheafComplexIso M U).hom.f n
  let η := CategoryTheory.toSheafify (Opens.grothendieckTopology X) P
  let ηQ := CategoryTheory.toSheafify (Opens.grothendieckTopology U) Q
  let ηT := CategoryTheory.toSheafify (Opens.grothendieckTopology U) T
  let a := η.app (op U)
  let b := (CategoryTheory.sheafify (Opens.grothendieckTopology X) P).map
    (nestedOpenTopIso X U).hom.op
  let c := (openSheafificationIso X U P).inv.hom.app (op ⊤)
  let d := (CategoryTheory.sheafifyMap (Opens.grothendieckTopology U) α).app (op ⊤)
  let r := P.map (nestedOpenTopIso X U).hom.op
  let s := η.app (op (ChartOpenDiffeomorph.nestedOpenImage U ⊤))
  let t := ηQ.app (op ⊤)
  let v := α.app (op ⊤)
  let w := ηT.app (op ⊤)
  let l := (Singular.Functor.singularPullback M (Opens.inclusion' (⊤ : Opens (TopCat.of U)))).f n
  have h1 : a ≫ b = r ≫ s := (η.naturality (nestedOpenTopIso X U).hom.op).symm
  have h2 : s ≫ c = t :=
    NatTrans.congr_app (openSheafificationIso_unit_inv X U P) (op ⊤)
  have h3 : t ≫ d = v ≫ w :=
    (NatTrans.congr_app (CategoryTheory.toSheafify_naturality
      (Opens.grothendieckTopology U) α) (op ⊤)).symm
  have h4 : r ≫ v = l := singularOpenTopPullback M X U n
  change a ≫ (b ≫ (c ≫ d)) = l ≫ w
  calc
    a ≫ (b ≫ (c ≫ d)) = ((a ≫ b) ≫ c) ≫ d := by simp only [Category.assoc]
    _ = ((r ≫ s) ≫ c) ≫ d := by rw [h1]
    _ = (r ≫ t) ≫ d := by rw [Category.assoc r s c, h2]
    _ = r ≫ (v ≫ w) := by rw [Category.assoc, h3]
    _ = l ≫ w := by rw [← Category.assoc, h4]

/-- Every ambient singular-sheaf section on a paracompact Hausdorff open
subset has an actual singular cochain representative on that subset. -/
theorem singularCochainsToOpenSheafSections_surjective_of_paracompact
    (M : ModuleCat.{0} R) (X : TopCat.{0}) (U : Opens X)
    [ParacompactSpace U] [T2Space U] (n : ℕ) :
    Function.Surjective ((singularCochainsToOpenSheafSections M X U).f n) := by
  intro s
  let e := (HomologicalComplex.eval (ModuleCat.{0} R) (ComplexShape.up ℕ) n).mapIso
    (singularSheafOpenSectionsIso M X U)
  obtain ⟨c, hc⟩ := ParacompactComparison.singularCochainsToSheafSections_surjective_of_paracompact
    M (TopCat.of U) n (e.hom s)
  refine ⟨c, e.toLinearEquiv.injective ?_⟩
  exact (ConcreteCategory.congr_hom
    (congrArg (fun f => f.f n) (singularSheafOpenSectionsIso_unit M X U)) c).trans hc

/-- The preceding representative theorem stated for the literal component
of the ambient presheaf-to-sheaf unit. -/
theorem singularCochain_sheafification_open_surjective_of_paracompact
    (M : ModuleCat.{0} R) (X : TopCat.{0}) (U : Opens X)
    [ParacompactSpace U] [T2Space U] (n : ℕ) :
    Function.Surjective
      ((CategoryTheory.toSheafify (Opens.grothendieckTopology X)
        (DeRham.Comparison.SingularPresheaf.singularCochainDegreePresheaf M X n)).app (op U)) :=
  singularCochainsToOpenSheafSections_surjective_of_paracompact M X U n

/-- The actual ambient open-section comparison is a quasi-isomorphism
over every characteristic-zero field on a paracompact Hausdorff open subset. -/
theorem quasiIso_singularCochainsToOpenSheafSections_of_paracompact
    (F : Type) [Field F] [CharZero F] (X : TopCat.{0}) (U : Opens X)
    [ParacompactSpace U] [T2Space U] :
    QuasiIso (singularCochainsToOpenSheafSections (ModuleCat.of F F) X U) := by
  let M := ModuleCat.of F F
  let e := singularSheafOpenSectionsIso M X U
  have : QuasiIso (singularCochainsToOpenSheafSections M X U ≫ e.hom) := by
    rw [show e = singularSheafOpenSectionsIso M X U from rfl,
      singularSheafOpenSectionsIso_unit]
    exact ParacompactComparison.quasiIso_singularCochainsToSheafSections_of_paracompact F (TopCat.of U)
  exact quasiIso_of_comp_right (singularCochainsToOpenSheafSections M X U) e.hom

end

end OAI.AlgebraicTopology.Cohomology.Singular.OpenSheafComparison

import OAI.AlgebraicTopology.Cohomology.Singular.ChartOpenDiffeomorph
import OAI.AlgebraicTopology.Cohomology.Singular.ChartSmoothComparison
import OAI.AlgebraicTopology.Cohomology.Singular.SmoothStalkComparison

/-! # Open Cochain Presheaf Comparison -/

namespace OAI.AlgebraicTopology.Cohomology.Singular.OpenCochainPresheafComparison

noncomputable section

/-!
# Cochains on an open subspace and restriction of ambient cochain presheaves

An open subset of an open subspace is identified with its actual ambient
image. The resulting homeomorphisms and diffeomorphisms give natural
isomorphisms of genuine ordinary and smooth singular cochain presheaves,
including their differentials and the ordinary-to-smooth restriction map.
-/

open _root_.CategoryTheory _root_.CategoryTheory.Limits Opposite _root_.TopologicalSpace
open scoped _root_.Manifold ContDiff Simplicial

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

variable {X : Type} [TopologicalSpace X]

/-- Send an open subset of an open subspace to its actual ambient open image. -/
def nestedOpenImageFunctor (W : Opens X) : Opens W ⥤ Opens X where
  obj := ChartOpenDiffeomorph.nestedOpenImage W
  map i := homOfLE (Set.image_mono i.le)
  map_id _ := Subsingleton.elim _ _
  map_comp _ _ := Subsingleton.elim _ _

@[simp]
theorem nestedOpenImageFunctor_obj (W : Opens X) (V : Opens W) :
    (nestedOpenImageFunctor W).obj V = ChartOpenDiffeomorph.nestedOpenImage W V := rfl

/-- The topological identification of nested and flattened open subspaces. -/
def nestedOpenHomeomorph (W : Opens X) (V : Opens W) : V ≃ₜ ChartOpenDiffeomorph.nestedOpenImage W V where
  toEquiv := ChartOpenDiffeomorph.nestedOpenEquiv W V
  continuous_toFun := (continuous_subtype_val.comp continuous_subtype_val).subtype_mk _
  continuous_invFun := (continuous_subtype_val.subtype_mk _).subtype_mk _

/-- Flattening nested opens commutes with their actual continuous inclusions. -/
theorem nestedOpenHomeomorph_naturality (W : Opens X) {U V : Opens W} (i : U ⟶ V) :
    (Opens.toTopCat (TopCat.of W)).map i ≫
        (TopCat.isoOfHomeo (nestedOpenHomeomorph W V)).hom =
      (TopCat.isoOfHomeo (nestedOpenHomeomorph W U)).hom ≫
        (Opens.toTopCat (TopCat.of X)).map ((nestedOpenImageFunctor W).map i) := rfl

variable {R : Type} [Ring R]

/-- Ordinary cochains on an open subspace agree naturally with the ambient
ordinary cochain presheaf restricted to its nested open images. -/
def singularOpenCochainPresheafIso (A : ModuleCat.{0} R) (W : Opens X) :
    (nestedOpenImageFunctor W).op ⋙ DeRham.Comparison.SingularPresheaf.singularCochainPresheaf A (TopCat.of X) ≅
      DeRham.Comparison.SingularPresheaf.singularCochainPresheaf A (TopCat.of W) :=
  NatIso.ofComponents
    (fun V => (Singular.Functor.singularCochainsFunctor A).mapIso
      (TopCat.isoOfHomeo (nestedOpenHomeomorph W V.unop)).op)
    (fun {U V} i => by
      change Singular.Functor.singularPullback A
          ((Opens.toTopCat (TopCat.of X)).map ((nestedOpenImageFunctor W).map i.unop)) ≫
          Singular.Functor.singularPullback A (TopCat.isoOfHomeo (nestedOpenHomeomorph W V.unop)).hom =
        Singular.Functor.singularPullback A (TopCat.isoOfHomeo (nestedOpenHomeomorph W U.unop)).hom ≫
          Singular.Functor.singularPullback A ((Opens.toTopCat (TopCat.of W)).map i.unop)
      rw [← Singular.Functor.singularPullback_comp, ← Singular.Functor.singularPullback_comp,
        nestedOpenHomeomorph_naturality])

@[simp]
theorem singularOpenCochainPresheafIso_hom_app (A : ModuleCat.{0} R)
    (W : Opens X) (V : Opens W) :
    (singularOpenCochainPresheafIso A W).hom.app (op V) =
      Singular.Functor.singularPullback A (TopCat.isoOfHomeo (nestedOpenHomeomorph W V)).hom := rfl

/-- Degreewise precomposition by the actual nested-open image functor. -/
def nestedOpenPresheafComplexFunctor (W : Opens X) :
    CochainComplex ((Opens X)ᵒᵖ ⥤ ModuleCat.{0} R) ℕ ⥤
      CochainComplex ((Opens W)ᵒᵖ ⥤ ModuleCat.{0} R) ℕ :=
  ((Functor.whiskeringLeft _ _ (ModuleCat.{0} R)).obj
    (nestedOpenImageFunctor W).op).mapHomologicalComplex (ComplexShape.up ℕ)

/-- The same ordinary comparison as an isomorphism of actual complexes of
module-valued presheaves, preserving every differential. -/
def singularOpenPresheafComplexIso (A : ModuleCat.{0} R) (W : Opens X) :
    (nestedOpenPresheafComplexFunctor W).obj
        (DeRham.Comparison.SingularPresheaf.singularPresheafComplex A (TopCat.of X)) ≅
      DeRham.Comparison.SingularPresheaf.singularPresheafComplex A (TopCat.of W) :=
  HomologicalComplex.Hom.isoOfComponents
    (fun n => Functor.isoWhiskerRight (singularOpenCochainPresheafIso A W)
      (HomologicalComplex.eval (ModuleCat.{0} R) (ComplexShape.up ℕ) n))
    (fun i j _ => by
      apply NatTrans.ext
      funext V
      exact ((singularOpenCochainPresheafIso A W).hom.app V).comm i j)

@[simp]
theorem singularOpenPresheafComplexIso_hom_f_app (A : ModuleCat.{0} R)
    (W : Opens X) (V : Opens W) (n : ℕ) :
    ((singularOpenPresheafComplexIso A W).hom.f n).app (op V) =
      ((singularOpenCochainPresheafIso A W).hom.app (op V)).f n := rfl

variable (E : Type) [NormedAddCommGroup E] [NormedSpace ℝ E]
variable (M : Type) [TopologicalSpace M] [ChartedSpace E M]

/-- Genuine smooth cochains on an open submanifold agree naturally with
the ambient smooth cochain presheaf on its actual nested-open images. -/
def manifoldSmoothOpenCochainPresheafIso (A : ModuleCat.{0} R) (W : Opens M) :
    (nestedOpenImageFunctor W).op ⋙ ManifoldSmoothPresheaf.manifoldSmoothCochainPresheaf E M A ≅
      ManifoldSmoothPresheaf.manifoldSmoothCochainPresheaf E W A :=
  NatIso.ofComponents
    (fun V => ChartSmoothComparison.manifoldSmoothCochainsDiffeomorphIso A (ChartOpenDiffeomorph.nestedOpenDiffeomorph E W V.unop))
    (fun {U V} i => by
      change Singular.Functor.simplicialPullback A
          ((ManifoldSmoothPresheaf.manifoldOpenSmoothSingularFunctor E M).map
            ((nestedOpenImageFunctor W).map i.unop)) ≫
          Singular.Functor.simplicialPullback A
            (ChartSmoothComparison.manifoldSmoothSingularDiffeomorphIso (ChartOpenDiffeomorph.nestedOpenDiffeomorph E W V.unop)).hom =
        Singular.Functor.simplicialPullback A
            (ChartSmoothComparison.manifoldSmoothSingularDiffeomorphIso (ChartOpenDiffeomorph.nestedOpenDiffeomorph E W U.unop)).hom ≫
          Singular.Functor.simplicialPullback A ((ManifoldSmoothPresheaf.manifoldOpenSmoothSingularFunctor E W).map i.unop)
      rw [← Singular.Functor.simplicialPullback_comp, ← Singular.Functor.simplicialPullback_comp]
      congr 1)

@[simp]
theorem manifoldSmoothOpenCochainPresheafIso_hom_app (A : ModuleCat.{0} R)
    (W : Opens M) (V : Opens W) :
    (manifoldSmoothOpenCochainPresheafIso E M A W).hom.app (op V) =
      ManifoldSmoothFunctor.manifoldSmoothPullback E E A (ChartOpenDiffeomorph.nestedOpenDiffeomorph E W V)
        (ChartOpenDiffeomorph.nestedOpenDiffeomorph E W V).contMDiff := rfl

/-- The ordinary and smooth natural identifications intertwine the actual
restriction from continuous simplices to smooth simplices. -/
theorem openCochainPresheafIso_restriction (A : ModuleCat.{0} R) (W : Opens M) :
    Functor.whiskerLeft (nestedOpenImageFunctor W).op
        (ManifoldSmoothPresheaf.manifoldSmoothRestrictionNatTrans E M A) ≫
        (manifoldSmoothOpenCochainPresheafIso E M A W).hom =
      (singularOpenCochainPresheafIso A W).hom ≫
        ManifoldSmoothPresheaf.manifoldSmoothRestrictionNatTrans E W A := by
  apply NatTrans.ext
  funext V
  exact (ManifoldSmoothFunctor.manifoldSmoothCochainRestriction_naturality A
    (ChartOpenDiffeomorph.nestedOpenDiffeomorph E W V.unop) (ChartOpenDiffeomorph.nestedOpenDiffeomorph E W V.unop).contMDiff).symm

/-- The native smooth comparison as an actual isomorphism of complexes of
module-valued presheaves on the open subspace. -/
def manifoldSmoothOpenPresheafComplexIso (A : ModuleCat.{0} R) (W : Opens M) :
    (nestedOpenPresheafComplexFunctor W).obj (ManifoldSmoothPresheaf.manifoldSmoothPresheafComplex E M A) ≅
      ManifoldSmoothPresheaf.manifoldSmoothPresheafComplex E W A :=
  HomologicalComplex.Hom.isoOfComponents
    (fun n => Functor.isoWhiskerRight (manifoldSmoothOpenCochainPresheafIso E M A W)
      (HomologicalComplex.eval (ModuleCat.{0} R) (ComplexShape.up ℕ) n))
    (fun i j _ => by
      apply NatTrans.ext
      funext V
      exact ((manifoldSmoothOpenCochainPresheafIso E M A W).hom.app V).comm i j)

@[simp]
theorem manifoldSmoothOpenPresheafComplexIso_hom_f_app (A : ModuleCat.{0} R)
    (W : Opens M) (V : Opens W) (n : ℕ) :
    ((manifoldSmoothOpenPresheafComplexIso E M A W).hom.f n).app (op V) =
      ((manifoldSmoothOpenCochainPresheafIso E M A W).hom.app (op V)).f n := rfl

/-- The isomorphisms of presheaf complexes preserve the actual ordinary-to-smooth
restriction morphism in every degree, as a commuting square of complexes. -/
theorem openPresheafComplexIso_restriction (A : ModuleCat.{0} R) (W : Opens M) :
    (nestedOpenPresheafComplexFunctor W).map (SmoothStalkComparison.manifoldSmoothPresheafRestriction E M A) ≫
        (manifoldSmoothOpenPresheafComplexIso E M A W).hom =
      (singularOpenPresheafComplexIso A W).hom ≫
        SmoothStalkComparison.manifoldSmoothPresheafRestriction E W A := by
  ext n : 1
  apply NatTrans.ext
  funext V
  exact congrArg (fun f => f.f n)
    (NatTrans.congr_app (openCochainPresheafIso_restriction E M A W) V)

end

end OAI.AlgebraicTopology.Cohomology.Singular.OpenCochainPresheafComparison

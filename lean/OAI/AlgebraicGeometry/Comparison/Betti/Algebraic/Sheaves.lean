import OAI.AlgebraicGeometry.Comparison.Betti.Algebraic.Forms
import OAI.AlgebraicGeometry.Foundations.Scheme.SpecScalarTransport
import OAI.AlgebraicGeometry.Betti.Scheme

/-! # Sheaves -/

namespace OAI.AlgebraicGeometry.Comparison.Betti.Algebraic.Sheaves

noncomputable section

section

/-!
# Algebraic forms on the actual Zariski site

The rings on opens are the scheme's structure-sheaf sections, with complex
scalars supplied by its structure morphism. The algebraic differential-form
complex is constructed sectionwise and sheafified. Its hypercohomology is
defined as morphisms from the constant complex sheaf in the derived category.
No comparison map or comparison theorem is assumed here.
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry Opposite _root_.TopologicalSpace

variable (X : Over Foundations.Scheme.ProjectiveSpace.complexBase)

/-- Smoothness, separatedness and finite type, with no properness hypothesis. -/
def IsSmoothComplexVariety : Prop :=
  Smooth X.hom ∧ IsSeparated X.hom ∧
    LocallyOfFiniteType X.hom ∧ QuasiCompact X.hom

local instance sectionAlgebra (U : X.left.Opens) : Algebra ℂ Γ(X.left, U) :=
  Foundations.Scheme.SpecScalarTransport.specSectionScalarAlgebra X.hom U

/-- The genuine restriction map, respecting the scalars from Spec ℂ. -/
def sectionRestriction {U V : X.left.Opensᵒᵖ} (f : U ⟶ V) :
    Γ(X.left, U.unop) →ₐ[ℂ] Γ(X.left, V.unop) where
  __ := (X.left.presheaf.map f).hom
  commutes' c := by
    change (X.left.presheaf.map f)
        ((X.hom.appLE ⊤ U.unop le_top) ((Scheme.ΓSpecIso (.of ℂ)).inv c)) =
      (X.hom.appLE ⊤ V.unop le_top) ((Scheme.ΓSpecIso (.of ℂ)).inv c)
    exact ConcreteCategory.congr_hom (X.hom.appLE_map le_top f)
      ((Scheme.ΓSpecIso (.of ℂ)).inv c)

/-- The actual structure presheaf, retaining its complex algebra structure. -/
def sectionAlgebraFunctor : X.left.Opensᵒᵖ ⥤ CommAlgCat.{0} ℂ where
  obj U := CommAlgCat.of ℂ Γ(X.left, U.unop)
  map f := CommAlgCat.ofHom (sectionRestriction X f)
  map_id U := by
    ext a
    change (X.left.presheaf.map (𝟙 U)) a = a
    rw [X.left.presheaf.map_id]
    rfl
  map_comp f g := by
    ext a
    change (X.left.presheaf.map (f ≫ g)) a =
      (X.left.presheaf.map g) ((X.left.presheaf.map f) a)
    rw [X.left.presheaf.map_comp]
    rfl

/-- Algebraic differential forms computed on the actual rings of sections. -/
def deRhamPresheafOfComplexes :
    X.left.Opensᵒᵖ ⥤ CochainComplex (ModuleCat.{0} ℂ) ℕ :=
  sectionAlgebraFunctor X ⋙ Forms.algebraicDeRhamFunctor

def formPresheaf (n : ℕ) : X.left.Opensᵒᵖ ⥤ ModuleCat.{0} ℂ :=
  deRhamPresheafOfComplexes X ⋙ HomologicalComplex.eval _ _ n

def presheafDifferential (n : ℕ) : formPresheaf X n ⟶ formPresheaf X (n + 1) where
  app U := ((deRhamPresheafOfComplexes X).obj U).d n (n + 1)
  naturality := fun _ _ f => ((deRhamPresheafOfComplexes X).map f).comm n (n + 1)

def deRhamPresheafComplex :
    CochainComplex (X.left.Opensᵒᵖ ⥤ ModuleCat.{0} ℂ) ℕ :=
  CochainComplex.of (formPresheaf X) (presheafDifferential X)
    (fun n => NatTrans.ext (funext (fun U =>
      ((deRhamPresheafOfComplexes X).obj U).d_comp_d n (n + 1) (n + 2))))

@[simp]
theorem deRhamPresheafComplex_d (n : ℕ) :
    (deRhamPresheafComplex X).d n (n + 1) = presheafDifferential X n :=
  CochainComplex.of_d (formPresheaf X) (presheafDifferential X) n

abbrev ComplexSheaves :=
  Sheaf (Opens.grothendieckTopology X.left) (ModuleCat.{0} ℂ)

/-- Sheafification of the algebraic differential-form complex. -/
def algebraicDeRhamSheafComplex : CochainComplex (ComplexSheaves X) ℕ :=
  ((presheafToSheaf (Opens.grothendieckTopology X.left) (ModuleCat.{0} ℂ)).mapHomologicalComplex
    (ComplexShape.up ℕ)).obj (deRhamPresheafComplex X)

/-- Extend each section complex by zero in negative degrees. -/
def deRhamPresheafOfComplexesInt :
    X.left.Opensᵒᵖ ⥤ CochainComplex (ModuleCat.{0} ℂ) ℤ :=
  deRhamPresheafOfComplexes X ⋙
    (ComplexShape.embeddingUpIntGE 0).extendFunctor (ModuleCat.{0} ℂ)

/-- Transpose the sectionwise integer complexes into a complex of presheaves. -/
def deRhamPresheafComplexInt :
    CochainComplex (X.left.Opensᵒᵖ ⥤ ModuleCat.{0} ℂ) ℤ where
  X n := deRhamPresheafOfComplexesInt X ⋙ HomologicalComplex.eval _ _ n
  d i j :=
    { app := fun U => ((deRhamPresheafOfComplexesInt X).obj U).d i j
      naturality := fun _ _ f => ((deRhamPresheafOfComplexesInt X).map f).comm i j }
  shape i j h := NatTrans.ext (funext (fun U =>
    ((deRhamPresheafOfComplexesInt X).obj U).shape i j h))
  d_comp_d' i j k _ _ := NatTrans.ext (funext (fun U =>
    ((deRhamPresheafOfComplexesInt X).obj U).d_comp_d i j k))

/-- The algebraic de Rham sheaf complex indexed by integers. Sheafification
is applied after extension on sections, so it also constructs the negative
zero terms without choosing any comparison isomorphism. -/
def algebraicDeRhamSheafComplexInt : CochainComplex (ComplexSheaves X) ℤ :=
  ((presheafToSheaf (Opens.grothendieckTopology X.left) (ModuleCat.{0} ℂ)).mapHomologicalComplex
    (ComplexShape.up ℤ)).obj (deRhamPresheafComplexInt X)

instance complexSheavesHasDerivedCategory : HasDerivedCategory.{1} (ComplexSheaves X) :=
  HasDerivedCategory.standard _

def constantComplexSheaf : ComplexSheaves X :=
  (constantSheaf (Opens.grothendieckTopology X.left) (ModuleCat.{0} ℂ)).obj
    (ModuleCat.of ℂ ℂ)

/-- Hypercohomology of the algebraic de Rham sheaf complex. The larger universe
comes from the standard constructed derived category; no smallness or
finite-dimensionality theorem is assumed. -/
def algebraicDeRham (n : ℕ) : ModuleCat.{1} ℂ :=
  ModuleCat.of ℂ
    ((DerivedCategory.singleFunctor (ComplexSheaves X) 0).obj (constantComplexSheaf X) ⟶
      ((DerivedCategory.Q.obj (algebraicDeRhamSheafComplexInt X))⟦(n : ℤ)⟧))

/-- Existing genuine complex singular cohomology, moved to the universe of
the standard derived-category construction without changing coefficients. -/
def betti (n : ℕ) : ModuleCat.{1} ℂ :=
  (ModuleCat.uliftFunctor.{1, 0} ℂ).obj (Betti.Scheme.schemeBetti (ModuleCat.of ℂ ℂ) X n)

def bettiPullback {X Y : Over Foundations.Scheme.ProjectiveSpace.complexBase} (f : X ⟶ Y) (n : ℕ) :
    betti Y n ⟶ betti X n :=
  (ModuleCat.uliftFunctor.{1, 0} ℂ).map (Betti.Scheme.schemeBettiMap (ModuleCat.of ℂ ℂ) n f)

end

/-! Exact inverse image on sheaves of complex vector spaces over the Zariski
spaces of complex schemes. All maps are the standard site constructions. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry _root_.TopologicalSpace

variable {X Y : Over Foundations.Scheme.ProjectiveSpace.complexBase} (f : X ⟶ Y)

def inverseImage : ComplexSheaves Y ⥤ ComplexSheaves X :=
  (Opens.map f.left.base).sheafPullback (ModuleCat.{0} ℂ)
    (Opens.grothendieckTopology Y.left) (Opens.grothendieckTopology X.left)

def directImage : ComplexSheaves X ⥤ ComplexSheaves Y :=
  (Opens.map f.left.base).sheafPushforwardContinuous (ModuleCat.{0} ℂ)
    (Opens.grothendieckTopology Y.left) (Opens.grothendieckTopology X.left)

def imageAdjunction : inverseImage f ⊣ directImage f :=
  (Opens.map f.left.base).sheafAdjunctionContinuous (ModuleCat.{0} ℂ)
    (Opens.grothendieckTopology Y.left) (Opens.grothendieckTopology X.left)

instance inverseImageIsLeftAdjoint : (inverseImage f).IsLeftAdjoint :=
  (imageAdjunction f).isLeftAdjoint

instance inverseImagePreservesFiniteLimits : PreservesFiniteLimits (inverseImage f) := by
  exact Functor.SmallCategories.instPreservesFiniteLimitsSheafSheafPullbackOfRepresentablyFlat
    (Opens.map f.left.base) (ModuleCat.{0} ℂ)
    (Opens.grothendieckTopology Y.left) (Opens.grothendieckTopology X.left)

instance inverseImagePreservesFiniteColimits : PreservesFiniteColimits (inverseImage f) :=
  inferInstance

instance inverseImageAdditive : (inverseImage f).Additive := by
  let := preservesBinaryBiproducts_of_preservesBinaryCoproducts (inverseImage f)
  exact (inverseImage f).additive_of_preservesBinaryBiproducts

def derivedInverseImage : DerivedCategory (ComplexSheaves Y) ⥤
    DerivedCategory (ComplexSheaves X) :=
  (inverseImage f).mapDerivedCategory

instance directImageLinear : (directImage f).Linear ℂ where
  map_smul := by intros; rfl

/-- The adjunction transfers complex linearity of direct image to inverse image. -/
instance inverseImageLinear : (inverseImage f).Linear ℂ where
  map_smul {M N} c g := by
    let adj := imageAdjunction f
    apply (adj.homEquiv M ((inverseImage f).obj N)).injective
    have hmap (k : M ⟶ N) :
        adj.homEquiv M ((inverseImage f).obj N) ((inverseImage f).map k) =
          k ≫ adj.unit.app N := by
      simpa only [Category.comp_id, adj.homEquiv_id] using
        adj.homEquiv_naturality_left k (𝟙 ((inverseImage f).obj N))
    rw [hmap, Linear.smul_comp, adj.homEquiv_unit,
      Functor.map_smul, Linear.comp_smul, ← adj.homEquiv_unit, hmap]

instance derivedInverseImageLinear : (derivedInverseImage f).Linear ℂ :=
  inferInstanceAs ((inverseImage f).mapDerivedCategory.Linear ℂ)

/-- Inverse image preserves the constant coefficient sheaf, by uniqueness
of the left adjoint to global sections. -/
def inverseImageConstantFunctorIso :
    constantSheaf (Opens.grothendieckTopology Y.left) (ModuleCat.{0} ℂ) ⋙
        inverseImage f ≅
      constantSheaf (Opens.grothendieckTopology X.left) (ModuleCat.{0} ℂ) := by
  have hT : IsTerminal ((Opens.map f.left.base).obj (⊤ : Y.left.Opens)) := by
    change IsTerminal (⊤ : X.left.Opens)
    exact isTerminalTop
  exact ((constantSheafAdj (Opens.grothendieckTopology Y.left)
      (ModuleCat.{0} ℂ) isTerminalTop).comp (imageAdjunction f)).leftAdjointUniq
    (constantSheafAdj (Opens.grothendieckTopology X.left) (ModuleCat.{0} ℂ) hT)

def inverseImageConstantIso :
    (inverseImage f).obj (constantComplexSheaf Y) ≅ constantComplexSheaf X :=
  (inverseImageConstantFunctorIso f).app (ModuleCat.of ℂ ℂ)

attribute [local instance] sectionAlgebra

/-- Pullback of regular functions along the given scheme morphism. -/
def sectionPullback (U : Y.left.Opens) :
    Γ(Y.left, U) →ₐ[ℂ] Γ(X.left, f.left ⁻¹ᵁ U) where
  __ := (f.left.app U).hom
  commutes' c := by
    change (f.left.app U)
        ((Y.hom.appLE ⊤ U le_top) ((Scheme.ΓSpecIso (.of ℂ)).inv c)) =
      (X.hom.appLE ⊤ (f.left ⁻¹ᵁ U) le_top) ((Scheme.ΓSpecIso (.of ℂ)).inv c)
    have h : Y.hom.appLE ⊤ U le_top ≫ f.left.app U =
        X.hom.appLE ⊤ (f.left ⁻¹ᵁ U) le_top := by
      have hcomp := Scheme.Hom.appLE_comp_appLE f.left Y.hom
        ⊤ U (f.left ⁻¹ᵁ U) le_top le_rfl
      have hbase := congrArg
        (fun g : X.left ⟶ Foundations.Scheme.ProjectiveSpace.complexBase => g.appLE ⊤ (f.left ⁻¹ᵁ U) le_top)
        (Over.w f)
      exact (congrArg (fun g => Y.hom.appLE ⊤ U le_top ≫ g)
        (f.left.app_eq_appLE (U := U))).trans (hcomp.trans hbase)
    exact ConcreteCategory.congr_hom h ((Scheme.ΓSpecIso (.of ℂ)).inv c)

theorem sectionPullback_naturality {U V : Y.left.Opensᵒᵖ} (i : U ⟶ V) :
    (sectionRestriction X ((Opens.map f.left.base).op.map i)).comp
        (sectionPullback f U.unop) =
      (sectionPullback f V.unop).comp (sectionRestriction Y i) := by
  ext a
  exact (ConcreteCategory.congr_hom (f.left.naturality i) a).symm

/-- Pullback of the entire presheaf complex, induced on every coefficient
by the actual pullback of regular functions. -/
def deRhamPresheafPullback : deRhamPresheafOfComplexes Y ⟶
    (Opens.map f.left.base).op ⋙ deRhamPresheafOfComplexes X where
  app U := Forms.complexPullback (sectionPullback f U.unop)
  naturality := fun U V i => by
    change Forms.complexPullback (sectionRestriction Y i) ≫
        Forms.complexPullback (sectionPullback f V.unop) =
      Forms.complexPullback (sectionPullback f U.unop) ≫
        Forms.complexPullback
          (sectionRestriction X ((Opens.map f.left.base).op.map i))
    rw [← Forms.complexPullback_comp, ← Forms.complexPullback_comp,
      sectionPullback_naturality]

end

end OAI.AlgebraicGeometry.Comparison.Betti.Algebraic.Sheaves

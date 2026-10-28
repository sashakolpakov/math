import OAI.AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId
import OAI.AlgebraicGeometry.Comparison.Betti.Complex.Adjunction
import OAI.AlgebraicGeometry.Comparison.Betti.Complex.Extension

/-! # Int -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.DeRham.Int

noncomputable section

/-! Contravariant pullback on Cohomology's actual de Rham hypercohomology over
an arbitrary coefficient field. The construction uses regular-function
pullback, sheafification, and exact inverse image, as in BettiComparison. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry _root_.TopologicalSpace

open OAI.AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal

variable {R : Type} [CommRing R]
  {X Y : Over (Spec (CommRingCat.of R))} (f : X ⟶ Y)

def inverseImage : AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.Sheaves R Y ⥤ AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.Sheaves R X :=
  (Opens.map f.left.base).sheafPullback (ModuleCat.{0} R)
    (Opens.grothendieckTopology Y.left) (Opens.grothendieckTopology X.left)

def directImage : AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.Sheaves R X ⥤ AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.Sheaves R Y :=
  (Opens.map f.left.base).sheafPushforwardContinuous (ModuleCat.{0} R)
    (Opens.grothendieckTopology Y.left) (Opens.grothendieckTopology X.left)

def imageAdjunction : inverseImage f ⊣ directImage f :=
  (Opens.map f.left.base).sheafAdjunctionContinuous (ModuleCat.{0} R)
    (Opens.grothendieckTopology Y.left) (Opens.grothendieckTopology X.left)

instance inverseImageIsLeftAdjoint : (inverseImage f).IsLeftAdjoint :=
  (imageAdjunction f).isLeftAdjoint

instance inverseImagePreservesFiniteLimits : PreservesFiniteLimits (inverseImage f) := by
  exact Functor.SmallCategories.instPreservesFiniteLimitsSheafSheafPullbackOfRepresentablyFlat
    (Opens.map f.left.base) (ModuleCat.{0} R)
    (Opens.grothendieckTopology Y.left) (Opens.grothendieckTopology X.left)

instance inverseImagePreservesFiniteColimits : PreservesFiniteColimits (inverseImage f) :=
  inferInstance

instance inverseImageAdditive : (inverseImage f).Additive := by
  let := preservesBinaryBiproducts_of_preservesBinaryCoproducts (inverseImage f)
  exact (inverseImage f).additive_of_preservesBinaryBiproducts

instance directImageIsRightAdjoint : (directImage f).IsRightAdjoint :=
  (imageAdjunction f).isRightAdjoint

instance directImageAdditive : (directImage f).Additive := by
  let := preservesBinaryBiproducts_of_preservesBinaryProducts (directImage f)
  exact (directImage f).additive_of_preservesBinaryBiproducts

instance directImageLinear : (directImage f).Linear R where
  map_smul := by intros; rfl

instance inverseImageLinear : (inverseImage f).Linear R where
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

def inverseImageConstantIso :
    (inverseImage f).obj (AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.coefficientSheaf R Y) ≅ AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.coefficientSheaf R X := by
  have hT : IsTerminal ((Opens.map f.left.base).obj (⊤ : Y.left.Opens)) := by
    change IsTerminal (⊤ : X.left.Opens)
    exact isTerminalTop
  exact (((constantSheafAdj (Opens.grothendieckTopology Y.left)
      (ModuleCat.{0} R) isTerminalTop).comp (imageAdjunction f)).leftAdjointUniq
    (constantSheafAdj (Opens.grothendieckTopology X.left) (ModuleCat.{0} R) hT)).app
      (ModuleCat.of R R)

def sectionPullback (U : Y.left.Opens) :
    Γ(Y.left, U) →ₐ[R] Γ(X.left, f.left ⁻¹ᵁ U) where
  __ := (f.left.app U).hom
  commutes' c := by
    change (f.left.app U)
        ((Y.hom.appLE ⊤ U le_top) ((Scheme.ΓSpecIso (.of R)).inv c)) =
      (X.hom.appLE ⊤ (f.left ⁻¹ᵁ U) le_top) ((Scheme.ΓSpecIso (.of R)).inv c)
    have h : Y.hom.appLE ⊤ U le_top ≫ f.left.app U =
        X.hom.appLE ⊤ (f.left ⁻¹ᵁ U) le_top := by
      have hcomp := Scheme.Hom.appLE_comp_appLE f.left Y.hom
        ⊤ U (f.left ⁻¹ᵁ U) le_top le_rfl
      have hbase := congrArg
        (fun g : X.left ⟶ Spec (.of R) => g.appLE ⊤ (f.left ⁻¹ᵁ U) le_top)
        (Over.w f)
      exact (congrArg (fun g => Y.hom.appLE ⊤ U le_top ≫ g)
        (f.left.app_eq_appLE (U := U))).trans (hcomp.trans hbase)
    exact ConcreteCategory.congr_hom h ((Scheme.ΓSpecIso (.of R)).inv c)

def directImagePresheaf : (X.left.Opensᵒᵖ ⥤ ModuleCat.{0} R) ⥤
    (Y.left.Opensᵒᵖ ⥤ ModuleCat.{0} R) :=
  (Functor.whiskeringLeft _ _ _).obj (Opens.map f.left.base).op

instance directImagePresheafAdditive : (directImagePresheaf f).Additive :=
  inferInstanceAs (((Functor.whiskeringLeft _ _ _).obj (Opens.map f.left.base).op).Additive)

def formsPullback (n : ℕ) : AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.formsPresheaf R Y n ⟶
    (directImagePresheaf f).obj (AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.formsPresheaf R X n) where
  app U := ModuleCat.ofHom (AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.formMap (CommAlgCat.ofHom (sectionPullback f U.unop)) n)
  naturality U V i := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro ω
    change AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.Form R Γ(Y.left, U.unop) n at ω
    change AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.formMap (CommAlgCat.ofHom (sectionPullback f V.unop)) n
        (AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.formMap ((AlgebraicGeometry.Crystalline.Cohomology.AlgebraicForms.AlgebraicDeRham.sectionAlgebras R Y).map i) n ω) =
      AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.formMap ((AlgebraicGeometry.Crystalline.Cohomology.AlgebraicForms.AlgebraicDeRham.sectionAlgebras R X).map
        ((Opens.map f.left.base).op.map i)) n
        (AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.formMap (CommAlgCat.ofHom (sectionPullback f U.unop)) n ω)
    have hmaps :
        (AlgebraicGeometry.Crystalline.Cohomology.AlgebraicForms.AlgebraicDeRham.sectionAlgebras R Y).map i ≫
            CommAlgCat.ofHom (sectionPullback f V.unop) =
          CommAlgCat.ofHom (sectionPullback f U.unop) ≫
            (AlgebraicGeometry.Crystalline.Cohomology.AlgebraicForms.AlgebraicDeRham.sectionAlgebras R X).map
              ((Opens.map f.left.base).op.map i) := by
      apply CommAlgCat.hom_ext
      apply AlgHom.ext
      intro a
      exact ConcreteCategory.congr_hom (f.left.naturality i) a
    exact (AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.formMap_comp ((AlgebraicGeometry.Crystalline.Cohomology.AlgebraicForms.AlgebraicDeRham.sectionAlgebras R Y).map i)
      (CommAlgCat.ofHom (sectionPullback f V.unop)) n ω).symm.trans
        ((congrArg (fun t => AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.formMap t n ω) hmaps).trans
          (AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.formMap_comp (CommAlgCat.ofHom (sectionPullback f U.unop))
            ((AlgebraicGeometry.Crystalline.Cohomology.AlgebraicForms.AlgebraicDeRham.sectionAlgebras R X).map
              ((Opens.map f.left.base).op.map i)) n ω))

def presheafPullback : AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.presheafComplex R Y ⟶
    ((directImagePresheaf f).mapHomologicalComplex (ComplexShape.up ℕ)).obj
      (AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.presheafComplex R X) :=
  CochainComplex.ofHom (formsPullback f) (fun n => by
    change formsPullback f n ≫ (directImagePresheaf f).map
        ((AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.presheafComplex R X).d n (n + 1)) =
      (AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.presheafComplex R Y).d n (n + 1) ≫ formsPullback f (n + 1)
    simp only [AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.presheafComplex, CochainComplex.of_d]
    apply NatTrans.ext
    funext U
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro ω
    change AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.Form R Γ(Y.left, U.unop) n at ω
    change AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.differential R Γ(X.left, f.left ⁻¹ᵁ U.unop) n
        (AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.formMap (CommAlgCat.ofHom (sectionPullback f U.unop)) n ω) =
      AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.formMap (CommAlgCat.ofHom (sectionPullback f U.unop)) (n + 1)
        (AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.differential R Γ(Y.left, U.unop) n ω)
    exact (AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.formMap_differential (CommAlgCat.ofHom (sectionPullback f U.unop)) n ω).symm)

def sheafificationComplexAdjunction (X : Over (Spec (CommRingCat.of R))) :
    (presheafToSheaf (Opens.grothendieckTopology X.left) (ModuleCat.{0} R)).mapHomologicalComplex
        (ComplexShape.up ℕ) ⊣
      (sheafToPresheaf (Opens.grothendieckTopology X.left) (ModuleCat.{0} R)).mapHomologicalComplex
        (ComplexShape.up ℕ) :=
  AlgebraicGeometry.Comparison.Betti.Complex.Adjunction.onComplexes
    (sheafificationAdjunction (Opens.grothendieckTopology X.left) (ModuleCat.{0} R))
    (ComplexShape.up ℕ)

def imageComplexAdjunction :
    (inverseImage f).mapHomologicalComplex (ComplexShape.up ℕ) ⊣
      (directImage f).mapHomologicalComplex (ComplexShape.up ℕ) :=
  AlgebraicGeometry.Comparison.Betti.Complex.Adjunction.onComplexes (imageAdjunction f) (ComplexShape.up ℕ)

def presheafToDirectImageSheafComplex : AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.presheafComplex R Y ⟶
    ((sheafToPresheaf (Opens.grothendieckTopology Y.left) (ModuleCat.{0} R)).mapHomologicalComplex
      (ComplexShape.up ℕ)).obj
      (((directImage f).mapHomologicalComplex (ComplexShape.up ℕ)).obj (AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.sheafComplex R X)) :=
  presheafPullback f ≫
    ((directImagePresheaf f).mapHomologicalComplex (ComplexShape.up ℕ)).map
      ((sheafificationComplexAdjunction X).unit.app (AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.presheafComplex R X))

def sheafDirectImage : AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.sheafComplex R Y ⟶
    ((directImage f).mapHomologicalComplex (ComplexShape.up ℕ)).obj (AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.sheafComplex R X) :=
  ((sheafificationComplexAdjunction Y).homEquiv (AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.presheafComplex R Y)
    (((directImage f).mapHomologicalComplex (ComplexShape.up ℕ)).obj
      (AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.sheafComplex R X))).symm (presheafToDirectImageSheafComplex f)

def sheafPullback :
    ((inverseImage f).mapHomologicalComplex (ComplexShape.up ℕ)).obj (AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.sheafComplex R Y) ⟶
      AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.sheafComplex R X :=
  ((imageComplexAdjunction f).homEquiv (AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.sheafComplex R Y)
    (AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.sheafComplex R X)).symm (sheafDirectImage f)

def sheafPullbackInt :
    ((inverseImage f).mapHomologicalComplex (ComplexShape.up ℤ)).obj (AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.sheafComplexInt R Y) ⟶
      AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.sheafComplexInt R X :=
  (AlgebraicGeometry.Comparison.Betti.Complex.Extension.mapExtendIso (inverseImage f) ComplexShape.embeddingUpNat
    (AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.sheafComplex R Y)).hom ≫
      HomologicalComplex.extendMap (Int.sheafPullback f) ComplexShape.embeddingUpNat

def derivedInverseImage : DerivedCategory (AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.Sheaves R Y) ⥤ DerivedCategory (AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.Sheaves R X) :=
  (inverseImage f).mapDerivedCategory

instance derivedInverseImageLinear : (derivedInverseImage f).Linear R :=
  inferInstanceAs ((inverseImage f).mapDerivedCategory.Linear R)

instance derivedInverseImageCommShift : (derivedInverseImage f).CommShift ℤ :=
  inferInstanceAs ((inverseImage f).mapDerivedCategory.CommShift ℤ)

instance derivedInverseImageAdditive : (derivedInverseImage f).Additive :=
  inferInstanceAs ((inverseImage f).mapDerivedCategory.Additive)

def derivedPullback :
    (derivedInverseImage f).obj (DerivedCategory.Q.obj (AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.sheafComplexInt R Y)) ⟶
      DerivedCategory.Q.obj (AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.sheafComplexInt R X) :=
  (inverseImage f).mapDerivedCategoryFactors.hom.app (AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.sheafComplexInt R Y) ≫
    DerivedCategory.Q.map (sheafPullbackInt f)

def derivedConstantIso :
    (derivedInverseImage f).obj
        ((DerivedCategory.singleFunctor (AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.Sheaves R Y) 0).obj (AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.coefficientSheaf R Y)) ≅
      (DerivedCategory.singleFunctor (AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.Sheaves R X) 0).obj (AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.coefficientSheaf R X) :=
  ((inverseImage f).mapDerivedCategorySingleFunctor 0).app (AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.coefficientSheaf R Y) ≪≫
    (DerivedCategory.singleFunctor (AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.Sheaves R X) 0).mapIso (inverseImageConstantIso f)

/-- Pullback written on the defining derived-category morphism spaces. -/
def rawPullback (n : ℕ) :
    ((DerivedCategory.singleFunctor (AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.Sheaves R Y) 0).obj (AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.coefficientSheaf R Y) ⟶
      (DerivedCategory.Q.obj (AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.sheafComplexInt R Y))⟦(n : ℤ)⟧) →ₗ[R]
    ((DerivedCategory.singleFunctor (AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.Sheaves R X) 0).obj (AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.coefficientSheaf R X) ⟶
      (DerivedCategory.Q.obj (AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.sheafComplexInt R X))⟦(n : ℤ)⟧) where
  toFun α :=
    (derivedConstantIso f).inv ≫ (derivedInverseImage f).map α ≫
      ((derivedInverseImage f).commShiftIso (n : ℤ)).hom.app
        (DerivedCategory.Q.obj (AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.sheafComplexInt R Y)) ≫
      (shiftFunctor (DerivedCategory (AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.Sheaves R X)) (n : ℤ)).map (derivedPullback f)
  map_add' α β := by
    simp only [Functor.map_add, Preadditive.comp_add, Preadditive.add_comp]
  map_smul' c α := by
    simp only [Functor.map_smul, Linear.comp_smul, Linear.smul_comp, RingHom.id_apply]

/-- The genuine pullback on Cohomology's algebraic de Rham hypercohomology. -/
def pullback (n : ℕ) : AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.cohomology R Y n →ₗ[R] AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.cohomology R X n := rawPullback f n

end

end OAI.NumberTheory.PadicHodge.GeometricComparison.DeRham.Int

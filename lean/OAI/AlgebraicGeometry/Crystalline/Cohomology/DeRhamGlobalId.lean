import OAI.AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo
import Mathlib.Algebra.Homology.Embedding.Extend
import Mathlib.Algebra.Homology.DerivedCategory.Linear
import Mathlib.CategoryTheory.Linear.FunctorCategory
import Mathlib.CategoryTheory.Sites.Abelian

/-! # De Rham Global Id -/

namespace OAI.AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal

noncomputable section

/-!
# Cohomology: the global algebraic de Rham complex

Restriction maps act on `a₀ da₁ ∧... ∧ daₙ` by applying the coordinate
algebra homomorphism to every factor. Their compatibility with exterior
differentiation is proved before sheafifying the complex. Global
hypercohomology is then defined in the derived category of sheaves.
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry Opposite

open OAI.AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation

universe u

variable {R : Type u} [CommRing R]

def rawMap {A B : CommAlgCat.{u} R} (f : A ⟶ B) (n : ℕ) :
    DeRhamPresentationTo.DeRhamPresentation.Raw A n →ₗ[R] DeRhamPresentationTo.DeRhamPresentation.Raw B n :=
  Finsupp.lsum R (fun v =>
    ((Finsupp.lsingle (R := B) (M := B) (fun i => f (v i))).restrictScalars R).comp
      f.hom.toLinearMap)

@[simp]
theorem rawMap_single {A B : CommAlgCat.{u} R} (f : A ⟶ B) (n : ℕ)
    (a : A) (v : Fin n → A) :
    rawMap f n (Finsupp.single v a) = Finsupp.single (fun i => f (v i)) (f a) := by
  rw [rawMap, Finsupp.lsum_single]
  rfl

theorem rawMap_smul {A B : CommAlgCat.{u} R} (f : A ⟶ B) (n : ℕ)
    (a : A) (v : DeRhamPresentationTo.DeRhamPresentation.Raw A n) : rawMap f n (a • v) = (f a) • rawMap f n v := by
  induction v using Finsupp.induction_linear with
  | zero => simp
  | add v w hv hw => simp only [smul_add, map_add, hv, hw]
  | single v b => simp [Finsupp.smul_single, smul_eq_mul, map_mul]

def mapRelation {A B : CommAlgCat.{u} R} (f : A ⟶ B) {n : ℕ} :
    DeRhamPresentationTo.DeRhamPresentation.RelationIndex R A n → DeRhamPresentationTo.DeRhamPresentation.RelationIndex R B n
  | .add v i x y => .add (fun j => f (v j)) i (f x) (f y)
  | .mul v i x y => .mul (fun j => f (v j)) i (f x) (f y)
  | .base v i r => .base (fun j => f (v j)) i r
  | .alt v i j hij hne => .alt (fun j => f (v j)) i j (congrArg f hij) hne

theorem map_tuple_update {A B : CommAlgCat.{u} R} (f : A ⟶ B) {n : ℕ}
    (v : Fin n → A) (i : Fin n) (a : A) :
    (fun j => f (Function.update v i a j)) =
      Function.update (fun j => f (v j)) i (f a) := by
  funext j
  by_cases h : j = i <;> simp [h]

@[simp]
theorem map_base {A B : CommAlgCat.{u} R} (f : A ⟶ B) (r : R) :
    f (algebraMap R A r) = algebraMap R B r := f.hom.commutes r

theorem rawMap_relation {A B : CommAlgCat.{u} R} (f : A ⟶ B) {n : ℕ}
    (r : DeRhamPresentationTo.DeRhamPresentation.RelationIndex R A n) :
    rawMap f n (DeRhamPresentationTo.DeRhamPresentation.relation R A n r) = DeRhamPresentationTo.DeRhamPresentation.relation R B n (mapRelation f r) := by
  cases r <;>
    simp only [DeRhamPresentationTo.DeRhamPresentation.relation, mapRelation, map_sub, rawMap_single, map_one, map_tuple_update,
      map_add, map_mul, map_base]

theorem rawMap_mem_relations {A B : CommAlgCat.{u} R} (f : A ⟶ B) {n : ℕ}
    (v : DeRhamPresentationTo.DeRhamPresentation.Raw A n) (hv : v ∈ DeRhamPresentationTo.DeRhamPresentation.relations R A n) : rawMap f n v ∈ DeRhamPresentationTo.DeRhamPresentation.relations R B n := by
  induction hv using Submodule.span_induction with
  | mem v hv =>
    obtain ⟨r, rfl⟩ := hv
    rw [rawMap_relation]
    exact Submodule.subset_span (Set.mem_range_self _)
  | zero => simp
  | add v w hv hw ihv ihw => rw [map_add]; exact Submodule.add_mem _ ihv ihw
  | smul a v hv ih => rw [rawMap_smul]; exact Submodule.smul_mem _ _ ih

/-- Pullback on the actual generators-and-relations forms. -/
def formMap {A B : CommAlgCat.{u} R} (f : A ⟶ B) (n : ℕ) :
    DeRhamPresentationTo.DeRhamPresentation.Form R A n →ₗ[R] DeRhamPresentationTo.DeRhamPresentation.Form R B n :=
  ((DeRhamPresentationTo.DeRhamPresentation.relations R A n).restrictScalars R).liftQ
    (((DeRhamPresentationTo.DeRhamPresentation.relations R B n).mkQ.restrictScalars R).comp (rawMap f n))
    (fun v hv => Submodule.Quotient.mk_eq_zero _ |>.mpr (rawMap_mem_relations f v hv))

@[simp]
theorem formMap_symbol {A B : CommAlgCat.{u} R} (f : A ⟶ B) (n : ℕ)
    (a : A) (v : Fin n → A) :
    formMap f n (DeRhamPresentationTo.DeRhamPresentation.symbol R A a v) = DeRhamPresentationTo.DeRhamPresentation.symbol R B (f a) (fun i => f (v i)) := by
  change (DeRhamPresentationTo.DeRhamPresentation.relations R B n).mkQ (rawMap f n (Finsupp.single v a)) = _
  rw [rawMap_single]
  rfl

@[simp]
theorem formMap_id (A : CommAlgCat.{u} R) (n : ℕ) (ω : DeRhamPresentationTo.DeRhamPresentation.Form R A n) :
    formMap (𝟙 A) n ω = ω := by
  obtain ⟨v, rfl⟩ := Submodule.mkQ_surjective (DeRhamPresentationTo.DeRhamPresentation.relations R A n) ω
  induction v using Finsupp.induction_linear with
  | zero => simp
  | add v w hv hw => simp only [map_add, hv, hw]
  | single v a => exact formMap_symbol (𝟙 A) n a v

theorem formMap_comp {A B C : CommAlgCat.{u} R} (f : A ⟶ B) (g : B ⟶ C)
    (n : ℕ) (ω : DeRhamPresentationTo.DeRhamPresentation.Form R A n) :
    formMap (f ≫ g) n ω = formMap g n (formMap f n ω) := by
  obtain ⟨v, rfl⟩ := Submodule.mkQ_surjective (DeRhamPresentationTo.DeRhamPresentation.relations R A n) ω
  induction v using Finsupp.induction_linear with
  | zero => simp
  | add v w hv hw => simp only [map_add, hv, hw]
  | single v a =>
    change formMap (f ≫ g) n (DeRhamPresentationTo.DeRhamPresentation.symbol R A a v) =
      formMap g n (formMap f n (DeRhamPresentationTo.DeRhamPresentation.symbol R A a v))
    simp only [formMap_symbol, CommAlgCat.comp_apply]

theorem formMap_differential {A B : CommAlgCat.{u} R} (f : A ⟶ B)
    (n : ℕ) (ω : DeRhamPresentationTo.DeRhamPresentation.Form R A n) :
    formMap f (n + 1) (DeRhamPresentationTo.DeRhamPresentation.differential R A n ω) = DeRhamPresentationTo.DeRhamPresentation.differential R B n (formMap f n ω) := by
  obtain ⟨v, rfl⟩ := Submodule.mkQ_surjective (DeRhamPresentationTo.DeRhamPresentation.relations R A n) ω
  induction v using Finsupp.induction_linear with
  | zero => simp
  | add v w hv hw => simp only [map_add, hv, hw]
  | single v a =>
    change formMap f (n + 1) (DeRhamPresentationTo.DeRhamPresentation.differential R A n (DeRhamPresentationTo.DeRhamPresentation.symbol R A a v)) =
      DeRhamPresentationTo.DeRhamPresentation.differential R B n (formMap f n (DeRhamPresentationTo.DeRhamPresentation.symbol R A a v))
    simp only [DeRhamPresentationTo.DeRhamPresentation.differential_symbol, formMap_symbol, map_one]
    apply congrArg (DeRhamPresentationTo.DeRhamPresentation.symbol R B 1)
    funext j
    refine Fin.cases (by simp) (fun j => by simp) j

def formsFunctor (n : ℕ) : CommAlgCat.{u} R ⥤ ModuleCat.{u} R where
  obj A := ModuleCat.of R (DeRhamPresentationTo.DeRhamPresentation.Form R A n)
  map f := ModuleCat.ofHom (formMap f n)
  map_id A := ModuleCat.hom_ext (LinearMap.ext (formMap_id A n))
  map_comp f g := ModuleCat.hom_ext (LinearMap.ext (formMap_comp f g n))

variable (R) (X : Over (Spec (CommRingCat.of R)))

def formsPresheaf (n : ℕ) : X.left.Opensᵒᵖ ⥤ ModuleCat.{u} R :=
  AlgebraicForms.AlgebraicDeRham.sectionAlgebras R X ⋙ formsFunctor n

def differentialPresheaf (n : ℕ) : formsPresheaf R X n ⟶ formsPresheaf R X (n + 1) where
  app U := ModuleCat.ofHom (DeRhamPresentationTo.DeRhamPresentation.differential R Γ(X.left, U.unop) n)
  naturality _U _V f := ModuleCat.hom_ext
    (LinearMap.ext (fun ω => (formMap_differential
      ((AlgebraicForms.AlgebraicDeRham.sectionAlgebras R X).map f) n ω).symm))

theorem differentialPresheaf_square (n : ℕ) :
    differentialPresheaf R X n ≫ differentialPresheaf R X (n + 1) = 0 := by
  apply NatTrans.ext
  funext U
  apply ModuleCat.hom_ext
  exact LinearMap.ext (DeRhamPresentationTo.DeRhamPresentation.differential_square R Γ(X.left, U.unop) n)

/-- The de Rham complex before sheafification. -/
def presheafComplex : CochainComplex (X.left.Opensᵒᵖ ⥤ ModuleCat.{u} R) ℕ :=
  CochainComplex.of (formsPresheaf R X) (differentialPresheaf R X)
    (differentialPresheaf_square R X)

abbrev Sheaves := Sheaf (Opens.grothendieckTopology X.left) (ModuleCat.{u} R)

/-- The global complex of sheaves, formed from the proved exterior differential. -/
def sheafComplex : CochainComplex (Sheaves R X) ℕ :=
  ((presheafToSheaf (Opens.grothendieckTopology X.left) (ModuleCat.{u} R)).mapHomologicalComplex
    (ComplexShape.up ℕ)).obj (presheafComplex R X)

/-- Extend by zero to negative degrees for the derived-category construction. -/
def sheafComplexInt : CochainComplex (Sheaves R X) ℤ :=
  (sheafComplex R X).extend ComplexShape.embeddingUpNat

instance derivedCategory : HasDerivedCategory.{u + 1} (Sheaves R X) :=
  HasDerivedCategory.standard _

def coefficientSheaf : Sheaves R X :=
  (constantSheaf (Opens.grothendieckTopology X.left) (ModuleCat.{u} R)).obj (ModuleCat.of R R)

/-- Hypercohomology of the global algebraic de Rham complex. -/
def cohomology (n : ℕ) : ModuleCat.{u + 1} R :=
  ModuleCat.of R
    (ShiftedHom ((DerivedCategory.singleFunctor (Sheaves R X) 0).obj (coefficientSheaf R X))
      (DerivedCategory.Q.obj (sheafComplexInt R X)) (n : ℤ))

end

end OAI.AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal

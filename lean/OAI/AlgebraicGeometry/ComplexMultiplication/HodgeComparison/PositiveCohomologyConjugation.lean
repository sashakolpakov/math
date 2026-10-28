import OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.CochainConjugation
import OAI.AlgebraicTopology.Cohomology.Singular.RationalComplex

/-! # Positive Cohomology Conjugation -/

namespace OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.PositiveCohomologyConjugation.CM.Construction

noncomputable section

section

/-! Scalar-restriction compatibility needed to identify the HodgeComparison real structure. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits Opposite
open OAI.AlgebraicTopology.Cohomology.Singular.RationalComplex
open scoped Simplicial

abbrev restrictToRational := ModuleCat.restrictScalars (algebraMap ℚ ℂ)

abbrev restrictComplex (K : CochainComplex (ModuleCat ℂ) ℕ) :=
  (restrictToRational.mapHomologicalComplex (ComplexShape.up ℕ)).obj K

/-- The same element is a cocycle after restriction of scalars. -/
def restrictCocycle (K : CochainComplex (ModuleCat ℂ) ℕ) (n : ℕ)
    (c : AlgebraicTopology.Cohomology.Singular.Representatives.cochainCocycles K n) : AlgebraicTopology.Cohomology.Singular.Representatives.cochainCocycles (restrictComplex K) n :=
  ⟨c.val, c.property⟩

/-- Exact scalar restriction carries the class of a cocycle to the class
of the same cocycle in the original coefficient module. -/
theorem restrictHomology_class (K : CochainComplex (ModuleCat ℂ) ℕ) (n : ℕ)
    (c : AlgebraicTopology.Cohomology.Singular.Representatives.cochainCocycles K n) :
    ((K.sc n).mapHomologyIso restrictToRational).hom
      (AlgebraicTopology.Cohomology.Singular.Representatives.cochainClass (restrictComplex K) n (restrictCocycle K n c)) =
        AlgebraicTopology.Cohomology.Singular.Representatives.cochainClass K n c := by
  let S := K.sc n
  let T := S.map restrictToRational
  let h := S.moduleCatLeftHomologyData
  let cq := restrictCocycle K n c
  have hc : (h.map restrictToRational).cyclesIso.hom
      (T.moduleCatCyclesIso.inv cq) = c := by
    apply Subtype.ext
    have h₁ := ConcreteCategory.congr_hom
      (h.map restrictToRational).cyclesIso_hom_comp_i (T.moduleCatCyclesIso.inv cq)
    have h₂ := ConcreteCategory.congr_hom T.moduleCatCyclesIso_inv_iCycles cq
    exact h₁.trans h₂
  have hπ := ConcreteCategory.congr_hom
    (h.map restrictToRational).homologyπ_comp_homologyIso_hom
      (T.moduleCatCyclesIso.inv cq)
  change (h.map restrictToRational).homologyIso.hom
      (AlgebraicTopology.Cohomology.Singular.Representatives.cochainClass (restrictComplex K) n cq) = (h.map restrictToRational).π
        ((h.map restrictToRational).cyclesIso.hom (T.moduleCatCyclesIso.inv cq)) at hπ
  rw [hc] at hπ
  rw [h.mapHomologyIso_eq restrictToRational]
  change h.homologyIso.inv
      ((h.map restrictToRational).homologyIso.hom
        (AlgebraicTopology.Cohomology.Singular.Representatives.cochainClass (restrictComplex K) n cq)) = _
  rw [hπ]
  rfl

/-- The native cochain scalar-restriction comparison leaves simplex values unchanged. -/
theorem restrictCochains_evaluation (S : SSet.{0}) (n : ℕ)
    (c : (AlgebraicTopology.Cohomology.Singular.Basic.simplicialCochains S (ModuleCat.of ℂ ℂ)).X n) (s : S _⦋n⦌) :
    AlgebraicTopology.Cohomology.Singular.Coefficients.simplicialEvaluation S (restrictToRational.obj (ModuleCat.of ℂ ℂ)) s
      ((AlgebraicTopology.Cohomology.Singular.Chains.simplicialCochainsRestrictScalarsIso (algebraMap ℚ ℂ) S
        (ModuleCat.of ℂ ℂ)).hom.f n c) =
      AlgebraicTopology.Cohomology.Singular.Coefficients.simplicialEvaluation S (ModuleCat.of ℂ ℂ) s c := by
  have h := congrArg Quiver.Hom.unop
    (ι_comp_sigmaComparison restrictToRational.op
      (fun _ : S _⦋n⦌ => op (ModuleCat.of ℂ ℂ)) s)
  exact ConcreteCategory.congr_hom h c

/-- The native rational-to-complex cochain map, with its target viewed over ℚ. -/
def rationalToComplexCochain (X : TopCat.{0}) :
    AlgebraicTopology.Cohomology.Singular.Basic.singularCochains (ModuleCat.of ℚ ℚ) X ⟶
      restrictComplex (AlgebraicTopology.Cohomology.Singular.Basic.singularCochains (ModuleCat.of ℂ ℂ) X) :=
  AlgebraicTopology.Cohomology.Singular.Coefficients.coefficientCochainMap (ModuleCat.ofHom AlgebraicTopology.Cohomology.Singular.RationalRetraction.rationalInclusion) X ≫
    AlgebraicTopology.Cohomology.Singular.Coefficients.coefficientCochainMap AlgebraicTopology.Cohomology.Singular.RationalComplex.complexCoefficientsRestrictionIso.hom X ≫
      (AlgebraicTopology.Cohomology.Singular.Chains.singularCochainsRestrictScalarsIso (algebraMap ℚ ℂ) (ModuleCat.of ℂ ℂ) X).inv

/-- This cochain map gives exactly the existing rational Betti inclusion. -/
theorem rationalToComplexCohomology_eq (X : TopCat.{0}) (n : ℕ) :
    AlgebraicTopology.Cohomology.Singular.RationalComplex.rationalToComplexCohomology X n =
      HomologicalComplex.homologyMap (rationalToComplexCochain X) n ≫
        (((AlgebraicTopology.Cohomology.Singular.Basic.singularCochains (ModuleCat.of ℂ ℂ) X).sc n).mapHomologyIso
          restrictToRational).hom := by
  simp only [AlgebraicTopology.Cohomology.Singular.RationalComplex.rationalToComplexCohomology, AlgebraicTopology.Cohomology.Singular.RationalInjection.rationalComplexCoefficientMap,
    AlgebraicTopology.Cohomology.Singular.RationalComplex.complexCohomologyRestrictionIso, AlgebraicTopology.Cohomology.Singular.Chains.singularCohomologyRestrictScalarsIso,
    rationalToComplexCochain, HomologicalComplex.homologyMap_comp]
  rfl

/-- A rational cocycle yields the same cocycle with complex coefficients. -/
def complexCocycleOfRational (X : TopCat.{0}) (n : ℕ)
    (c : AlgebraicTopology.Cohomology.Singular.Representatives.singularCocycles (ModuleCat.of ℚ ℚ) X n) :
    AlgebraicTopology.Cohomology.Singular.Representatives.singularCocycles (ModuleCat.of ℂ ℂ) X n :=
  let cq := AlgebraicTopology.Cohomology.Singular.RepresentativesNaturality.cochainCocycleMap (rationalToComplexCochain X) n c
  ⟨cq.val, cq.property⟩

/-- The rational inclusion preserves the actual class of the represented cocycle. -/
theorem rationalToComplexCohomology_class (X : TopCat.{0}) (n : ℕ)
    (c : AlgebraicTopology.Cohomology.Singular.Representatives.singularCocycles (ModuleCat.of ℚ ℚ) X n) :
    AlgebraicTopology.Cohomology.Singular.RationalComplex.rationalToComplexCohomology X n (AlgebraicTopology.Cohomology.Singular.Representatives.singularClass (ModuleCat.of ℚ ℚ) X n c) =
      AlgebraicTopology.Cohomology.Singular.Representatives.singularClass (ModuleCat.of ℂ ℂ) X n (complexCocycleOfRational X n c) := by
  rw [rationalToComplexCohomology_eq]
  change (((AlgebraicTopology.Cohomology.Singular.Basic.singularCochains (ModuleCat.of ℂ ℂ) X).sc n).mapHomologyIso
    restrictToRational).hom
      (HomologicalComplex.homologyMap (rationalToComplexCochain X) n
        (AlgebraicTopology.Cohomology.Singular.Representatives.cochainClass (AlgebraicTopology.Cohomology.Singular.Basic.singularCochains (ModuleCat.of ℚ ℚ) X) n c)) = _
  rw [AlgebraicTopology.Cohomology.Singular.RepresentativesNaturality.cochainClass_naturality]
  exact restrictHomology_class _ n (complexCocycleOfRational X n c)

/-- The native coefficient inclusion casts each rational simplex value to ℂ. -/
theorem rationalToComplexCochain_evaluation (X : TopCat.{0}) (n : ℕ)
    (c : (AlgebraicTopology.Cohomology.Singular.Basic.singularCochains (ModuleCat.of ℚ ℚ) X).X n) (s : AlgebraicTopology.Cohomology.Singular.Basic.singularSimplices X n) :
    AlgebraicTopology.Cohomology.Singular.Coefficients.simplicialEvaluation (TopCat.toSSet.obj X) (ModuleCat.of ℂ ℂ) s
      ((rationalToComplexCochain X).f n c) =
        (AlgebraicTopology.Cohomology.Singular.Coefficients.simplicialEvaluation (TopCat.toSSet.obj X) (ModuleCat.of ℚ ℚ) s c : ℂ) := by
  let e := AlgebraicTopology.Cohomology.Singular.Chains.singularCochainsRestrictScalarsIso (algebraMap ℚ ℂ) (ModuleCat.of ℂ ℂ) X
  let cr := (AlgebraicTopology.Cohomology.Singular.Coefficients.coefficientCochainMap (ModuleCat.ofHom AlgebraicTopology.Cohomology.Singular.RationalRetraction.rationalInclusion) X).f n c
  let y := (AlgebraicTopology.Cohomology.Singular.Coefficients.coefficientCochainMap AlgebraicTopology.Cohomology.Singular.RationalComplex.complexCoefficientsRestrictionIso.hom X).f n cr
  have he : e.hom.f n (e.inv.f n y) = y :=
    ConcreteCategory.congr_hom (congrArg (fun g => g.f n) e.inv_hom_id) y
  have h := restrictCochains_evaluation (TopCat.toSSet.obj X) n
    ((rationalToComplexCochain X).f n c) s
  change AlgebraicTopology.Cohomology.Singular.Coefficients.simplicialEvaluation (TopCat.toSSet.obj X)
    (restrictToRational.obj (ModuleCat.of ℂ ℂ)) s (e.hom.f n (e.inv.f n y)) = _ at h
  rw [he] at h
  have h₁ := ConcreteCategory.congr_hom
    (AlgebraicTopology.Cohomology.Singular.Coefficients.coefficientCochainMap_evaluation AlgebraicTopology.Cohomology.Singular.RationalComplex.complexCoefficientsRestrictionIso.hom X s) cr
  have h₂ := ConcreteCategory.congr_hom
    (AlgebraicTopology.Cohomology.Singular.Coefficients.coefficientCochainMap_evaluation (ModuleCat.ofHom AlgebraicTopology.Cohomology.Singular.RationalRetraction.rationalInclusion) X s) c
  exact h.symm.trans (h₁.trans h₂)

/-- A complex cocycle coming from rational coefficients is fixed by conjugation. -/
theorem conjugate_complexCocycleOfRational (X : TopCat.{0}) (n : ℕ)
    (c : AlgebraicTopology.Cohomology.Singular.Representatives.singularCocycles (ModuleCat.of ℚ ℚ) X n) :
    CochainConjugation.CM.Construction.conjugateSimplicialCochain (TopCat.toSSet.obj X) n
      (complexCocycleOfRational X n c).val = (complexCocycleOfRational X n c).val := by
  apply (AlgebraicTopology.Cohomology.Singular.Coefficients.degreewiseFunctionIso (TopCat.toSSet.obj X)
    (ModuleCat.of ℂ ℂ) n).toLinearEquiv.injective
  funext s
  change (AlgebraicTopology.Cohomology.Singular.Coefficients.degreewiseFunctionIso (TopCat.toSSet.obj X) (ModuleCat.of ℂ ℂ) n).hom _ s =
    (AlgebraicTopology.Cohomology.Singular.Coefficients.degreewiseFunctionIso (TopCat.toSSet.obj X) (ModuleCat.of ℂ ℂ) n).hom _ s
  rw [CochainConjugation.CM.Construction.conjugateSimplicialCochain_function]
  rw [AlgebraicTopology.Cohomology.Singular.Coefficients.degreewiseFunctionIso_hom_apply]
  change star (AlgebraicTopology.Cohomology.Singular.Coefficients.simplicialEvaluation (TopCat.toSSet.obj X) (ModuleCat.of ℂ ℂ) s
    ((rationalToComplexCochain X).f n c.val)) =
      AlgebraicTopology.Cohomology.Singular.Coefficients.simplicialEvaluation (TopCat.toSSet.obj X) (ModuleCat.of ℂ ℂ) s
        ((rationalToComplexCochain X).f n c.val)
  rw [rationalToComplexCochain_evaluation]
  exact map_ratCast (starRingEnd ℂ) _

/-- Actual singular-cochain conjugation fixes the image of rational H¹. -/
theorem conjugateSimplicialH1_rational (X : TopCat.{0})
    (a : AlgebraicTopology.Cohomology.Singular.Basic.singularCohomology (ModuleCat.of ℚ ℚ) X 1) :
    CochainConjugation.CM.Construction.conjugateSimplicialH1 (TopCat.toSSet.obj X) (AlgebraicTopology.Cohomology.Singular.RationalComplex.rationalToComplexCohomology X 1 a) =
      AlgebraicTopology.Cohomology.Singular.RationalComplex.rationalToComplexCohomology X 1 a := by
  obtain ⟨c, rfl⟩ := AlgebraicTopology.Cohomology.Singular.Representatives.singularClass_surjective (ModuleCat.of ℚ ℚ) X 1 a
  rw [rationalToComplexCohomology_class]
  unfold CochainConjugation.CM.Construction.conjugateSimplicialH1
  rw [CochainConjugation.CM.Construction.semilinearH1Map_class]
  apply congrArg (AlgebraicTopology.Cohomology.Singular.Representatives.cochainClass (AlgebraicTopology.Cohomology.Singular.Basic.singularCochains (ModuleCat.of ℂ ℂ) X) 1)
  apply Subtype.ext
  exact conjugate_complexCocycleOfRational X 1 c

end

/-! Actual semilinear comparison and coefficient conjugation in every
positive cohomological degree, needed for the real Kähler functional. -/

open _root_.CategoryTheory OAI.AlgebraicTopology.Cohomology.Singular.RationalComplex

section Semilinear

variable (K L : CochainComplex (ModuleCat ℂ) ℕ) (σ : ℂ →+* ℂ)
  (f : ∀ m, K.X m →ₛₗ[σ] L.X m)
  (hf : ∀ m x, f (m + 1) (K.d m (m + 1) x) = L.d m (m + 1) (f m x)) (n : ℕ)

def semilinearSuccCocycleMap : AlgebraicTopology.Cohomology.Singular.Representatives.cochainCocycles K (n + 1) →ₛₗ[σ] AlgebraicTopology.Cohomology.Singular.Representatives.cochainCocycles L (n + 1) where
  toFun c := ⟨f (n + 1) c.val, by
    rw [AlgebraicTopology.Cohomology.Singular.Representatives.mem_cochainCocycles_iff, ← hf]
    have hc := (AlgebraicTopology.Cohomology.Singular.Representatives.mem_cochainCocycles_iff K (n + 1) c.val).mp c.property
    rw [hc, map_zero]⟩
  map_add' a b := Subtype.ext ((f (n + 1)).map_add a.val b.val)
  map_smul' c a := Subtype.ext ((f (n + 1)).map_smulₛₗ c a.val)

theorem semilinearSuccCocycleMap_preserves_boundaries :
    AlgebraicTopology.Cohomology.Singular.Representatives.cochainBoundaries K (n + 1) ≤ (AlgebraicTopology.Cohomology.Singular.Representatives.cochainBoundaries L (n + 1)).comap
      (semilinearSuccCocycleMap K L σ f hf n) := by
  intro c hc
  have hcz : AlgebraicTopology.Cohomology.Singular.Representatives.cochainClass K (n + 1) c = AlgebraicTopology.Cohomology.Singular.Representatives.cochainClass K (n + 1) 0 := by
    rw [(AlgebraicTopology.Cohomology.Singular.Representatives.cochainClass_eq_zero_iff K (n + 1) c).mpr hc, map_zero]
  obtain ⟨b, hb⟩ := (AlgebraicTopology.Cohomology.Singular.Representatives.cochainClass_eq_iff_exists_succ K n c 0).mp hcz
  apply (AlgebraicTopology.Cohomology.Singular.Representatives.cochainClass_eq_zero_iff L (n + 1) _).mp
  rw [← (AlgebraicTopology.Cohomology.Singular.Representatives.cochainClass L (n + 1)).map_zero]
  apply (AlgebraicTopology.Cohomology.Singular.Representatives.cochainClass_eq_iff_exists_succ L n _ 0).mpr
  refine ⟨f n b, ?_⟩
  change L.d n (n + 1) (f n b) = f (n + 1) c.val - 0
  rw [sub_zero, ← hf]
  exact congrArg (f (n + 1)) (hb.trans (sub_zero c.val))

def semilinearHSuccMap : K.homology (n + 1) →ₛₗ[σ] L.homology (n + 1) :=
  (AlgebraicTopology.Cohomology.Singular.Representatives.cohomologyQuotientIso L (n + 1)).toLinearEquiv.symm.toLinearMap.comp
    (((AlgebraicTopology.Cohomology.Singular.Representatives.cochainBoundaries K (n + 1)).mapQ (AlgebraicTopology.Cohomology.Singular.Representatives.cochainBoundaries L (n + 1))
      (semilinearSuccCocycleMap K L σ f hf n)
      (semilinearSuccCocycleMap_preserves_boundaries K L σ f hf n)).comp
        (AlgebraicTopology.Cohomology.Singular.Representatives.cohomologyQuotientIso K (n + 1)).toLinearEquiv.toLinearMap)

theorem semilinearHSuccMap_class (c : AlgebraicTopology.Cohomology.Singular.Representatives.cochainCocycles K (n + 1)) :
    semilinearHSuccMap K L σ f hf n (AlgebraicTopology.Cohomology.Singular.Representatives.cochainClass K (n + 1) c) =
      AlgebraicTopology.Cohomology.Singular.Representatives.cochainClass L (n + 1) (semilinearSuccCocycleMap K L σ f hf n c) := by
  unfold semilinearHSuccMap AlgebraicTopology.Cohomology.Singular.Representatives.cochainClass
  simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.apply_symm_apply]
  rfl

end Semilinear

theorem semilinearHSuccMap_naturality
    (K L : CochainComplex (ModuleCat ℂ) ℕ) (σ : ℂ →+* ℂ)
    (f : ∀ m, K.X m →ₛₗ[σ] K.X m)
    (hf : ∀ m x, f (m + 1) (K.d m (m + 1) x) = K.d m (m + 1) (f m x))
    (g : ∀ m, L.X m →ₛₗ[σ] L.X m)
    (hg : ∀ m x, g (m + 1) (L.d m (m + 1) x) = L.d m (m + 1) (g m x))
    (n : ℕ) (a : K ⟶ L) (ha : ∀ x, g (n + 1) (a.f (n + 1) x) = a.f (n + 1) (f (n + 1) x))
    (x : K.homology (n + 1)) :
    semilinearHSuccMap L L σ g hg n (HomologicalComplex.homologyMap a (n + 1) x) =
      HomologicalComplex.homologyMap a (n + 1) (semilinearHSuccMap K K σ f hf n x) := by
  obtain ⟨c, rfl⟩ := AlgebraicTopology.Cohomology.Singular.Representatives.cochainClass_surjective K (n + 1) x
  rw [AlgebraicTopology.Cohomology.Singular.RepresentativesNaturality.cochainClass_naturality, semilinearHSuccMap_class,
    semilinearHSuccMap_class, AlgebraicTopology.Cohomology.Singular.RepresentativesNaturality.cochainClass_naturality]
  apply congrArg (AlgebraicTopology.Cohomology.Singular.Representatives.cochainClass L (n + 1))
  apply Subtype.ext
  exact ha c.val

def conjugateSimplicialHSucc (S : SSet.{0}) (n : ℕ) :
    (AlgebraicTopology.Cohomology.Singular.Basic.simplicialCochains S (ModuleCat.of ℂ ℂ)).homology (n + 1) →ₛₗ[starRingEnd ℂ]
      (AlgebraicTopology.Cohomology.Singular.Basic.simplicialCochains S (ModuleCat.of ℂ ℂ)).homology (n + 1) :=
  semilinearHSuccMap _ _ (starRingEnd ℂ)
    (CochainConjugation.CM.Construction.conjugateSimplicialCochain S) (CochainConjugation.CM.Construction.conjugateSimplicialCochain_d S) n

theorem conjugateSimplicialHSucc_pullback {S T : SSet.{0}} (a : S ⟶ T) (n : ℕ)
    (x : (AlgebraicTopology.Cohomology.Singular.Basic.simplicialCochains T (ModuleCat.of ℂ ℂ)).homology (n + 1)) :
    conjugateSimplicialHSucc S n
      (HomologicalComplex.homologyMap (AlgebraicTopology.Cohomology.Singular.Functor.simplicialPullback (ModuleCat.of ℂ ℂ) a) (n + 1) x) =
    HomologicalComplex.homologyMap (AlgebraicTopology.Cohomology.Singular.Functor.simplicialPullback (ModuleCat.of ℂ ℂ) a) (n + 1)
      (conjugateSimplicialHSucc T n x) :=
  semilinearHSuccMap_naturality _ _ (starRingEnd ℂ)
    (CochainConjugation.CM.Construction.conjugateSimplicialCochain T) (CochainConjugation.CM.Construction.conjugateSimplicialCochain_d T)
    (CochainConjugation.CM.Construction.conjugateSimplicialCochain S) (CochainConjugation.CM.Construction.conjugateSimplicialCochain_d S) n
    (AlgebraicTopology.Cohomology.Singular.Functor.simplicialPullback (ModuleCat.of ℂ ℂ) a) (CochainConjugation.CM.Construction.conjugateSimplicialCochain_pullback a (n + 1)) x

theorem conjugateSimplicialHSucc_rational (X : TopCat.{0}) (n : ℕ)
    (a : AlgebraicTopology.Cohomology.Singular.Basic.singularCohomology (ModuleCat.of ℚ ℚ) X (n + 1)) :
    conjugateSimplicialHSucc (TopCat.toSSet.obj X) n (AlgebraicTopology.Cohomology.Singular.RationalComplex.rationalToComplexCohomology X (n + 1) a) =
      AlgebraicTopology.Cohomology.Singular.RationalComplex.rationalToComplexCohomology X (n + 1) a := by
  obtain ⟨c, rfl⟩ := AlgebraicTopology.Cohomology.Singular.Representatives.singularClass_surjective (ModuleCat.of ℚ ℚ) X (n + 1) a
  rw [rationalToComplexCohomology_class]
  unfold conjugateSimplicialHSucc
  rw [semilinearHSuccMap_class]
  apply congrArg (AlgebraicTopology.Cohomology.Singular.Representatives.cochainClass (AlgebraicTopology.Cohomology.Singular.Basic.singularCochains (ModuleCat.of ℂ ℂ) X) (n + 1))
  apply Subtype.ext
  exact conjugate_complexCocycleOfRational X (n + 1) c

end

end OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.PositiveCohomologyConjugation.CM.Construction

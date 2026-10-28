import OAI.AlgebraicTopology.Cohomology.Singular.Formulas
import OAI.AlgebraicTopology.Cohomology.Singular.RepresentativesNaturality
import Mathlib.Basic.Complex.Basic

/-! # Cochain Conjugation -/

namespace OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.CochainConjugation.CM.Construction

noncomputable section

/-! Actual conjugation on simplicial cochains and degree-one cohomology for HodgeComparison. -/

open _root_.CategoryTheory
open scoped Simplicial

section Semilinear

variable (K L : CochainComplex (ModuleCat ℂ) ℕ) (σ : ℂ →+* ℂ)
  (f : ∀ n, K.X n →ₛₗ[σ] L.X n)
  (hf : ∀ n x, f (n + 1) (K.d n (n + 1) x) = L.d n (n + 1) (f n x))

/-- A graded semilinear map commuting with differentials maps one-cocycles
to one-cocycles. -/
def semilinearOneCocycleMap : AlgebraicTopology.Cohomology.Singular.Representatives.cochainCocycles K 1 →ₛₗ[σ] AlgebraicTopology.Cohomology.Singular.Representatives.cochainCocycles L 1 where
  toFun c := ⟨f 1 c.val, by
    rw [AlgebraicTopology.Cohomology.Singular.Representatives.mem_cochainCocycles_iff, ← hf]
    have hc : K.d 1 2 c.val = 0 := (AlgebraicTopology.Cohomology.Singular.Representatives.mem_cochainCocycles_iff K 1 c.val).mp c.property
    rw [hc, map_zero]⟩
  map_add' a b := Subtype.ext ((f 1).map_add a.val b.val)
  map_smul' c a := Subtype.ext ((f 1).map_smulₛₗ c a.val)

/-- Commutation in degree zero also preserves the one-coboundaries. -/
theorem semilinearOneCocycleMap_preserves_boundaries :
    AlgebraicTopology.Cohomology.Singular.Representatives.cochainBoundaries K 1 ≤ (AlgebraicTopology.Cohomology.Singular.Representatives.cochainBoundaries L 1).comap
      (semilinearOneCocycleMap K L σ f hf) := by
  intro c hc
  have hcz : AlgebraicTopology.Cohomology.Singular.Representatives.cochainClass K 1 c = AlgebraicTopology.Cohomology.Singular.Representatives.cochainClass K 1 0 := by
    rw [(AlgebraicTopology.Cohomology.Singular.Representatives.cochainClass_eq_zero_iff K 1 c).mpr hc, map_zero]
  obtain ⟨b, hb⟩ := (AlgebraicTopology.Cohomology.Singular.Representatives.cochainClass_eq_iff_exists_succ K 0 c 0).mp hcz
  apply (AlgebraicTopology.Cohomology.Singular.Representatives.cochainClass_eq_zero_iff L 1 _).mp
  rw [← (AlgebraicTopology.Cohomology.Singular.Representatives.cochainClass L 1).map_zero]
  apply (AlgebraicTopology.Cohomology.Singular.Representatives.cochainClass_eq_iff_exists_succ L 0 _ 0).mpr
  refine ⟨f 0 b, ?_⟩
  change L.d 0 1 (f 0 b) = f 1 c.val - 0
  rw [sub_zero, ← hf]
  exact congrArg (f 1) (hb.trans (sub_zero c.val))

/-- The induced semilinear map on the genuine categorical H¹, using its
existing cocycles-modulo-coboundaries presentation. -/
def semilinearH1Map : K.homology 1 →ₛₗ[σ] L.homology 1 :=
  (AlgebraicTopology.Cohomology.Singular.Representatives.cohomologyQuotientIso L 1).toLinearEquiv.symm.toLinearMap.comp
    (((AlgebraicTopology.Cohomology.Singular.Representatives.cochainBoundaries K 1).mapQ (AlgebraicTopology.Cohomology.Singular.Representatives.cochainBoundaries L 1)
      (semilinearOneCocycleMap K L σ f hf)
      (semilinearOneCocycleMap_preserves_boundaries K L σ f hf)).comp
        (AlgebraicTopology.Cohomology.Singular.Representatives.cohomologyQuotientIso K 1).toLinearEquiv.toLinearMap)

theorem semilinearH1Map_class (c : AlgebraicTopology.Cohomology.Singular.Representatives.cochainCocycles K 1) :
    semilinearH1Map K L σ f hf (AlgebraicTopology.Cohomology.Singular.Representatives.cochainClass K 1 c) =
      AlgebraicTopology.Cohomology.Singular.Representatives.cochainClass L 1 (semilinearOneCocycleMap K L σ f hf c) := by
  unfold semilinearH1Map AlgebraicTopology.Cohomology.Singular.Representatives.cochainClass
  simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.apply_symm_apply]
  rfl

end Semilinear

/-- A commuting square of graded maps gives the corresponding commuting
square on the actual degree-one cohomology. -/
theorem semilinearH1Map_naturality
    (K L : CochainComplex (ModuleCat ℂ) ℕ) (σ : ℂ →+* ℂ)
    (f : ∀ n, K.X n →ₛₗ[σ] K.X n)
    (hf : ∀ n x, f (n + 1) (K.d n (n + 1) x) = K.d n (n + 1) (f n x))
    (g : ∀ n, L.X n →ₛₗ[σ] L.X n)
    (hg : ∀ n x, g (n + 1) (L.d n (n + 1) x) = L.d n (n + 1) (g n x))
    (a : K ⟶ L) (ha : ∀ x, g 1 (a.f 1 x) = a.f 1 (f 1 x))
    (x : K.homology 1) :
    semilinearH1Map L L σ g hg (HomologicalComplex.homologyMap a 1 x) =
      HomologicalComplex.homologyMap a 1 (semilinearH1Map K K σ f hf x) := by
  obtain ⟨c, rfl⟩ := AlgebraicTopology.Cohomology.Singular.Representatives.cochainClass_surjective K 1 x
  rw [AlgebraicTopology.Cohomology.Singular.RepresentativesNaturality.cochainClass_naturality, semilinearH1Map_class,
    semilinearH1Map_class, AlgebraicTopology.Cohomology.Singular.RepresentativesNaturality.cochainClass_naturality]
  apply congrArg (AlgebraicTopology.Cohomology.Singular.Representatives.cochainClass L 1)
  apply Subtype.ext
  exact ha c.val

/-- Pointwise conjugation of complex-valued functions. -/
def conjugateFunctions (ι : Type*) : (ι → ℂ) →ₛₗ[starRingEnd ℂ] (ι → ℂ) where
  toFun f i := star (f i)
  map_add' f g := funext fun i => star_add (f i) (g i)
  map_smul' c f := funext fun i => map_mul (starRingEnd ℂ) c (f i)

/-- Conjugation of the values of a genuine simplicial cochain. -/
def conjugateSimplicialCochain (S : SSet.{0}) (n : ℕ) :
    (AlgebraicTopology.Cohomology.Singular.Basic.simplicialCochains S (ModuleCat.of ℂ ℂ)).X n →ₛₗ[starRingEnd ℂ]
      (AlgebraicTopology.Cohomology.Singular.Basic.simplicialCochains S (ModuleCat.of ℂ ℂ)).X n :=
  (AlgebraicTopology.Cohomology.Singular.Coefficients.degreewiseFunctionIso S (ModuleCat.of ℂ ℂ) n).toLinearEquiv.symm.toLinearMap.comp
    ((conjugateFunctions (S _⦋n⦌)).comp
      (AlgebraicTopology.Cohomology.Singular.Coefficients.degreewiseFunctionIso S (ModuleCat.of ℂ ℂ) n).toLinearEquiv.toLinearMap)

@[simp]
theorem conjugateSimplicialCochain_function (S : SSet.{0}) (n : ℕ)
    (c : (AlgebraicTopology.Cohomology.Singular.Basic.simplicialCochains S (ModuleCat.of ℂ ℂ)).X n) (s : S _⦋n⦌) :
    (AlgebraicTopology.Cohomology.Singular.Coefficients.degreewiseFunctionIso S (ModuleCat.of ℂ ℂ) n).hom
        (conjugateSimplicialCochain S n c) s =
      star ((AlgebraicTopology.Cohomology.Singular.Coefficients.degreewiseFunctionIso S (ModuleCat.of ℂ ℂ) n).hom c s) := by
  change (AlgebraicTopology.Cohomology.Singular.Coefficients.degreewiseFunctionIso S (ModuleCat.of ℂ ℂ) n).toLinearEquiv
    ((AlgebraicTopology.Cohomology.Singular.Coefficients.degreewiseFunctionIso S (ModuleCat.of ℂ ℂ) n).toLinearEquiv.symm _) s = _
  rw [LinearEquiv.apply_symm_apply]
  rfl

/-- The alternating-face differential has real signs, so it commutes with
conjugation of the values. -/
theorem conjugateSimplicialCochain_d (S : SSet.{0}) (n : ℕ)
    (c : (AlgebraicTopology.Cohomology.Singular.Basic.simplicialCochains S (ModuleCat.of ℂ ℂ)).X n) :
    conjugateSimplicialCochain S (n + 1)
        ((AlgebraicTopology.Cohomology.Singular.Basic.simplicialCochains S (ModuleCat.of ℂ ℂ)).d n (n + 1) c) =
      (AlgebraicTopology.Cohomology.Singular.Basic.simplicialCochains S (ModuleCat.of ℂ ℂ)).d n (n + 1)
        (conjugateSimplicialCochain S n c) := by
  apply (AlgebraicTopology.Cohomology.Singular.Coefficients.degreewiseFunctionIso S (ModuleCat.of ℂ ℂ) (n + 1)).toLinearEquiv.injective
  funext s
  change (AlgebraicTopology.Cohomology.Singular.Coefficients.degreewiseFunctionIso S (ModuleCat.of ℂ ℂ) (n + 1)).hom _ s =
    (AlgebraicTopology.Cohomology.Singular.Coefficients.degreewiseFunctionIso S (ModuleCat.of ℂ ℂ) (n + 1)).hom _ s
  rw [conjugateSimplicialCochain_function, AlgebraicTopology.Cohomology.Singular.Formulas.degreewiseFunctionIso_coboundary,
    AlgebraicTopology.Cohomology.Singular.Formulas.degreewiseFunctionIso_coboundary]
  change (starRingEnd ℂ) (∑ i : Fin (n + 2), ((-1 : ℤ) ^ i.val) •
    (AlgebraicTopology.Cohomology.Singular.Coefficients.degreewiseFunctionIso S (ModuleCat.of ℂ ℂ) n).hom c (S.δ i s)) = _
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [conjugateSimplicialCochain_function]
  exact map_zsmul (starRingEnd ℂ) _ _

/-- Conjugation on the actual degree-one simplicial cohomology. -/
def conjugateSimplicialH1 (S : SSet.{0}) :
    (AlgebraicTopology.Cohomology.Singular.Basic.simplicialCochains S (ModuleCat.of ℂ ℂ)).homology 1 →ₛₗ[starRingEnd ℂ]
      (AlgebraicTopology.Cohomology.Singular.Basic.simplicialCochains S (ModuleCat.of ℂ ℂ)).homology 1 :=
  semilinearH1Map _ _ (starRingEnd ℂ)
    (conjugateSimplicialCochain S) (conjugateSimplicialCochain_d S)

/-- Conjugating values commutes with precomposition on simplices. -/
theorem conjugateSimplicialCochain_pullback {S T : SSet.{0}} (a : S ⟶ T)
    (n : ℕ) (c : (AlgebraicTopology.Cohomology.Singular.Basic.simplicialCochains T (ModuleCat.of ℂ ℂ)).X n) :
    conjugateSimplicialCochain S n ((AlgebraicTopology.Cohomology.Singular.Functor.simplicialPullback (ModuleCat.of ℂ ℂ) a).f n c) =
      (AlgebraicTopology.Cohomology.Singular.Functor.simplicialPullback (ModuleCat.of ℂ ℂ) a).f n (conjugateSimplicialCochain T n c) := by
  apply (AlgebraicTopology.Cohomology.Singular.Coefficients.degreewiseFunctionIso S (ModuleCat.of ℂ ℂ) n).toLinearEquiv.injective
  funext s
  change (AlgebraicTopology.Cohomology.Singular.Coefficients.degreewiseFunctionIso S (ModuleCat.of ℂ ℂ) n).hom _ s =
    (AlgebraicTopology.Cohomology.Singular.Coefficients.degreewiseFunctionIso S (ModuleCat.of ℂ ℂ) n).hom _ s
  rw [conjugateSimplicialCochain_function, AlgebraicTopology.Cohomology.Singular.Formulas.degreewiseFunctionIso_pullback,
    AlgebraicTopology.Cohomology.Singular.Formulas.degreewiseFunctionIso_pullback, conjugateSimplicialCochain_function]

/-- The cohomological conjugation is natural for actual simplicial pullback. -/
theorem conjugateSimplicialH1_pullback {S T : SSet.{0}} (a : S ⟶ T)
    (x : (AlgebraicTopology.Cohomology.Singular.Basic.simplicialCochains T (ModuleCat.of ℂ ℂ)).homology 1) :
    conjugateSimplicialH1 S
        (HomologicalComplex.homologyMap (AlgebraicTopology.Cohomology.Singular.Functor.simplicialPullback (ModuleCat.of ℂ ℂ) a) 1 x) =
      HomologicalComplex.homologyMap (AlgebraicTopology.Cohomology.Singular.Functor.simplicialPullback (ModuleCat.of ℂ ℂ) a) 1
        (conjugateSimplicialH1 T x) :=
  semilinearH1Map_naturality _ _ (starRingEnd ℂ)
    (conjugateSimplicialCochain T) (conjugateSimplicialCochain_d T)
    (conjugateSimplicialCochain S) (conjugateSimplicialCochain_d S)
    (AlgebraicTopology.Cohomology.Singular.Functor.simplicialPullback (ModuleCat.of ℂ ℂ) a) (conjugateSimplicialCochain_pullback a 1) x

end

end OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.CochainConjugation.CM.Construction

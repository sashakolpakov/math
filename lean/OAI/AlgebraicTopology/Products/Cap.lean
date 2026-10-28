import OAI.AlgebraicTopology.Cohomology.Singular.EvaluationNaturality
import OAI.AlgebraicTopology.Products.SimplexFaceIdentities

/-! # Cap -/

namespace OAI.AlgebraicTopology.Products.Cap

noncomputable section

/-!
# The simplicial cap product

The cap product evaluates the cochain on the front face and retains the back
face of a simplex. All chains and cochains are the actual simplicial complexes
used for singular (co)homology.
-/

open _root_.CategoryTheory
open scoped Simplicial
open OAI.AlgebraicTopology.Cohomology.Singular.EvaluationNaturality

variable {R : Type} [CommRing R]

/-- Transport an actual chain along equality of its degree. -/
def chainCast (K : SSet.{0}) {a b : ℕ} (h : a = b) :
    (Cohomology.Singular.ChainDual.simplicialScalarChains (R := R) K).X a →ₗ[R]
      (Cohomology.Singular.ChainDual.simplicialScalarChains (R := R) K).X b :=
  (eqToHom (congrArg (Cohomology.Singular.ChainDual.simplicialScalarChains (R := R) K).X h)).hom

@[simp]
theorem chainCast_rfl (K : SSet.{0}) (n : ℕ) :
    chainCast (R := R) K (rfl : n = n) = LinearMap.id := rfl

@[simp]
theorem chainCast_simplex (K : SSet.{0}) {a b : ℕ} (h : a = b) (s : K _⦋a⦌) :
    chainCast (R := R) K h (Cohomology.Singular.ChainDual.simplexChain K s) = Cohomology.Singular.ChainDual.simplexChain K (SimplexFaceIdentities.simplexCast K h s) := by
  subst b
  rfl

/-- The cap product on actual simplicial chains: evaluate on the front face
and retain the back face. It is linear in both the cochain and chain. -/
def cap (K : SSet.{0}) (p q : ℕ) :
    (Cohomology.Singular.Basic.simplicialCochains K (ModuleCat.of R R)).X p →ₗ[R]
      (Cohomology.Singular.ChainDual.simplicialScalarChains (R := R) K).X (p + q) →ₗ[R]
        (Cohomology.Singular.ChainDual.simplicialScalarChains (R := R) K).X q where
  toFun c := Cohomology.Singular.ChainDual.chainFunctionalOfFunction K ((Cohomology.Singular.ChainDual.simplicialScalarChains (R := R) K).X q)
    (p + q) fun s =>
      Cohomology.Singular.Coefficients.simplicialEvaluation K (ModuleCat.of R R) (SimplexFaceIdentities.frontFace K p q s) c •
        Cohomology.Singular.ChainDual.simplexChain K (SimplexFaceIdentities.backFace K p q s)
  map_add' c d := by
    apply Cohomology.Singular.ChainDual.chainFunctional_ext K ((Cohomology.Singular.ChainDual.simplicialScalarChains (R := R) K).X q)
    intro s
    simp only [Cohomology.Singular.ChainDual.chainFunctionalOfFunction_simplex, LinearMap.add_apply, map_add, add_smul]
  map_smul' r c := by
    apply Cohomology.Singular.ChainDual.chainFunctional_ext K ((Cohomology.Singular.ChainDual.simplicialScalarChains (R := R) K).X q)
    intro s
    simp only [Cohomology.Singular.ChainDual.chainFunctionalOfFunction_simplex, LinearMap.smul_apply, map_smul,
      RingHom.id_apply, smul_smul, smul_eq_mul]

@[simp]
theorem cap_simplex (K : SSet.{0}) (p q : ℕ)
    (c : (Cohomology.Singular.Basic.simplicialCochains K (ModuleCat.of R R)).X p) (s : K _⦋p + q⦌) :
    cap K p q c (Cohomology.Singular.ChainDual.simplexChain K s) =
      Cohomology.Singular.Coefficients.simplicialEvaluation K (ModuleCat.of R R) (SimplexFaceIdentities.frontFace K p q s) c •
        Cohomology.Singular.ChainDual.simplexChain K (SimplexFaceIdentities.backFace K p q s) :=
  Cohomology.Singular.ChainDual.chainFunctionalOfFunction_simplex K ((Cohomology.Singular.ChainDual.simplicialScalarChains (R := R) K).X q)
    (p + q) _ s

/-- Cap products commute with pushforward of chains and pullback of cochains. -/
theorem cap_naturality {K L : SSet.{0}} (f : K ⟶ L) (p q : ℕ)
    (c : (Cohomology.Singular.Basic.simplicialCochains L (ModuleCat.of R R)).X p) :
    ((Cohomology.Singular.EvaluationNaturality.simplicialScalarChainMap (R := R) f).f q).hom.comp
        (cap K p q (((Cohomology.Singular.Functor.simplicialPullback (ModuleCat.of R R) f).f p) c)) =
      (cap L p q c).comp ((Cohomology.Singular.EvaluationNaturality.simplicialScalarChainMap (R := R) f).f (p + q)).hom := by
  apply Cohomology.Singular.ChainDual.chainFunctional_ext K ((Cohomology.Singular.ChainDual.simplicialScalarChains (R := R) L).X q)
  intro s
  simp only [LinearMap.comp_apply, cap_simplex, map_smul, Cohomology.Singular.EvaluationNaturality.simplicialScalarChainMap_simplex,
    SimplexFaceIdentities.frontFace_naturality, SimplexFaceIdentities.backFace_naturality]
  exact congrArg (fun r : R => r • Cohomology.Singular.ChainDual.simplexChain (R := R) L (f.app _ (SimplexFaceIdentities.backFace K p q s)))
    (Cohomology.Singular.Formulas.evaluation_pullback_apply (ModuleCat.of R R) f c (SimplexFaceIdentities.frontFace K p q s))

/-- The cap product on genuine continuous singular cochains and chains. -/
abbrev singularCap (X : TopCat.{0}) (p q : ℕ) :
    (Cohomology.Singular.Basic.singularCochains (ModuleCat.of R R) X).X p →ₗ[R]
      (Cohomology.Singular.Evaluation.singularScalarChains (R := R) X).X (p + q) →ₗ[R]
        (Cohomology.Singular.Evaluation.singularScalarChains (R := R) X).X q :=
  cap (TopCat.toSSet.obj X) p q

/-- The singular cap product is natural for continuous maps. -/
theorem singularCap_naturality {X Y : TopCat.{0}} (f : X ⟶ Y) (p q : ℕ)
    (c : (Cohomology.Singular.Basic.singularCochains (ModuleCat.of R R) Y).X p) :
    ((Cohomology.Singular.EvaluationNaturality.singularScalarChainMap (R := R) f).f q).hom.comp
        (singularCap X p q (((Cohomology.Singular.Functor.singularPullback (ModuleCat.of R R) f).f p) c)) =
      (singularCap Y p q c).comp ((Cohomology.Singular.EvaluationNaturality.singularScalarChainMap (R := R) f).f (p + q)).hom :=
  cap_naturality (TopCat.toSSet.map f) p q c

/-- A cochain with values in degree-`q` chains, sending each simplex to its
own elementary chain. -/
def simplexCochain (K : SSet.{0}) (q : ℕ) :
    (Cohomology.Singular.Basic.simplicialCochains K ((Cohomology.Singular.ChainDual.simplicialScalarChains (R := R) K).X q)).X q :=
  (Cohomology.Singular.Coefficients.degreewiseFunctionIso K ((Cohomology.Singular.ChainDual.simplicialScalarChains (R := R) K).X q) q).toLinearEquiv.symm
    (Cohomology.Singular.ChainDual.simplexChain K)

@[simp]
theorem simplexCochain_evaluation (K : SSet.{0}) (q : ℕ) (s : K _⦋q⦌) :
    Cohomology.Singular.Coefficients.simplicialEvaluation K ((Cohomology.Singular.ChainDual.simplicialScalarChains (R := R) K).X q) s
      (simplexCochain K q) = Cohomology.Singular.ChainDual.simplexChain (R := R) K s := by
  rw [← Cohomology.Singular.Coefficients.degreewiseFunctionIso_hom_apply]
  change ((Cohomology.Singular.Coefficients.degreewiseFunctionIso K ((Cohomology.Singular.ChainDual.simplicialScalarChains (R := R) K).X q) q).toLinearEquiv
    ((Cohomology.Singular.Coefficients.degreewiseFunctionIso K ((Cohomology.Singular.ChainDual.simplicialScalarChains (R := R) K).X q) q).toLinearEquiv.symm
      (Cohomology.Singular.ChainDual.simplexChain K))) s = _
  rw [LinearEquiv.apply_symm_apply]

/-- The universal chain-valued cochain represents the identity on chains. -/
theorem simplexCochain_dual (K : SSet.{0}) (q : ℕ) :
    Cohomology.Singular.ChainDual.degreewiseChainDualEquiv K ((Cohomology.Singular.ChainDual.simplicialScalarChains (R := R) K).X q) q
      (simplexCochain K q) = LinearMap.id := by
  apply Cohomology.Singular.ChainDual.chainFunctional_ext K ((Cohomology.Singular.ChainDual.simplicialScalarChains (R := R) K).X q)
  intro s
  simp

/-- The coboundary of the universal chain-valued cochain represents the actual
chain boundary. -/
theorem simplexCochain_coboundary_dual (K : SSet.{0}) (q : ℕ) :
    Cohomology.Singular.ChainDual.degreewiseChainDualEquiv K ((Cohomology.Singular.ChainDual.simplicialScalarChains (R := R) K).X q) (q + 1)
      ((Cohomology.Singular.Basic.simplicialCochains K ((Cohomology.Singular.ChainDual.simplicialScalarChains (R := R) K).X q)).d q (q + 1)
        (simplexCochain K q)) =
      ((Cohomology.Singular.ChainDual.simplicialScalarChains (R := R) K).d (q + 1) q).hom := by
  rw [Cohomology.Singular.ChainDual.degreewiseChainDualEquiv_coboundary, simplexCochain_dual, LinearMap.id_comp]

end

end OAI.AlgebraicTopology.Products.Cap

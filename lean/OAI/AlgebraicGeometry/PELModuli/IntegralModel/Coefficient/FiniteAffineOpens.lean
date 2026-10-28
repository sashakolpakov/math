import OAI.AlgebraicGeometry.PELModuli.IntegralModel.Coefficient.FixedAffineOpen
import OAI.AlgebraicGeometry.PELModuli.IntegralModel.Coefficient.OpenEnlargement

/-! # Finite Affine Opens -/

namespace OAI.AlgebraicGeometry.PELModuli.IntegralModel.Coefficient.FiniteAffineOpens.Coefficients

noncomputable section

/-! Finitely many affine opens spread inside one fixed ambient
coefficient model at a common finite stage, with their exact generic opens. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

variable {R K : Type} [CommRing R] [Field K] [Algebra R K]

theorem finite_affine_opens_in_fixed_model {I : Type} [Finite I]
    {X : Over (Spec (.of K))} (hX : ArithmeticGeometry.Models.Scheme.Constructions.Foundations.FinitePresentationMorphism X.hom)
    (M : Models.Coefficients.CoefficientModel R K X) (U : I → X.left.Opens) (hU : ∀ i, IsAffineOpen (U i)) :
    ∃ (t : Finset K) (h : M.coefficients ⊆ t)
      (V : I → ((Over.pullback (ArithmeticGeometry.Models.CoefficientSystem.Constructions.Foundations.coefficientBaseMap R K h)).obj M.model).left.Opens),
      (∀ i, IsAffineOpen (V i)) ∧
      (∀ i, Morphisms.Coefficients.genericModelLift M.model M.specialization M.cartesian.w h ⁻¹ᵁ V i = U i) := by
  classical
  let : Fintype I := Fintype.ofFinite I
  choose t ht V hV hpre using fun i => FixedAffineOpen.Coefficients.affine_open_in_fixed_model hX M (U i) (hU i)
  let z := M.coefficients ∪ Finset.univ.biUnion t
  have htz (i : I) : t i ⊆ z :=
    (Finset.subset_biUnion_of_mem t (Finset.mem_univ i)).trans Finset.subset_union_right
  exact ⟨z, Finset.subset_union_left,
    fun i => OpenEnlargement.Coefficients.enlargedModelOpen M (ht i) (htz i) (V i),
    fun i => OpenEnlargement.Coefficients.enlargedModelOpen_affine M (ht i) (htz i) (V i) (hV i),
    fun i => (OpenEnlargement.Coefficients.enlargedModelOpen_generic M (ht i) (htz i) (V i)).trans (hpre i)⟩

end

end OAI.AlgebraicGeometry.PELModuli.IntegralModel.Coefficient.FiniteAffineOpens.Coefficients

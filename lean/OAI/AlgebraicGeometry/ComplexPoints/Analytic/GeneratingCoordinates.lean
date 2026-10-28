import OAI.AlgebraicGeometry.ComplexPoints.Analytic.Affine
import Mathlib.Topology.Algebra.MvPolynomial

/-! # Generating Coordinates -/

namespace OAI.AlgebraicGeometry

/-!
# Independence of the generating coordinates

If a family generates a complex algebra, evaluation on that family induces the
ordinary topology on its complex points. The proof expresses each algebra
element as a multivariate polynomial in the generators. Consequently a finite
generating family realizes this topology inside ordinary finite-dimensional
complex affine space, and the topology is independent of the chosen family.
-/

universe u v w z

variable {A : Type u} [CommRing A] [Algebra ℂ A]
variable {ι : Type v} {κ : Type w}

/-- Coordinates of an affine complex point on a family of algebra elements. -/
def Foundations.Scheme.AffineComplexPoints.affineComplexPoints.coordinates (g : ι → A) (x : Foundations.Scheme.AffineComplexPoints.affineComplexPoints A) : ι → ℂ :=
  fun i => x (g i)

/-- Evaluating any family of regular functions is continuous. -/
@[continuity, fun_prop]
theorem Foundations.Scheme.AffineComplexPoints.affineComplexPoints.continuous_coordinates (g : ι → A) : Continuous (Foundations.Scheme.AffineComplexPoints.affineComplexPoints.coordinates g) :=
  continuous_pi fun i => Foundations.Scheme.AffineComplexPoints.affineComplexPoints.continuous_eval (g i)

/-- A generating family gives a surjective polynomial presentation. -/
theorem Foundations.Scheme.AffineComplexPoints.affineComplexPoints.aeval_surjective_of_adjoin_eq_top (g : ι → A)
    (hg : Algebra.adjoin ℂ (Set.range g) = ⊤) :
    Function.Surjective (MvPolynomial.aeval g : MvPolynomial ι ℂ →ₐ[ℂ] A) := by
  rw [← AlgHom.range_eq_top, ← Algebra.adjoin_range_eq_range_aeval]
  exact hg

/-- A regular-function evaluation is polynomial evaluation in the coordinates. -/
theorem Foundations.Scheme.AffineComplexPoints.affineComplexPoints.eval_aeval (g : ι → A) (p : MvPolynomial ι ℂ) :
    Foundations.Scheme.AffineComplexPoints.affineComplexPoints.eval (MvPolynomial.aeval g p) =
      fun x : Foundations.Scheme.AffineComplexPoints.affineComplexPoints A => MvPolynomial.eval (Foundations.Scheme.AffineComplexPoints.affineComplexPoints.coordinates g x) p := by
  funext x
  exact MvPolynomial.comp_aeval_apply g x p

/-- Generating coordinates induce exactly the ordinary topology on complex points. -/
theorem Foundations.Scheme.AffineComplexPoints.affineComplexPoints.isInducing_coordinates (g : ι → A)
    (hg : Algebra.adjoin ℂ (Set.range g) = ⊤) :
    Topology.IsInducing (Foundations.Scheme.AffineComplexPoints.affineComplexPoints.coordinates g) := by
  constructor
  apply le_antisymm (Foundations.Scheme.AffineComplexPoints.affineComplexPoints.continuous_coordinates g).le_induced
  change TopologicalSpace.induced (Foundations.Scheme.AffineComplexPoints.affineComplexPoints.coordinates g) inferInstance ≤
    TopologicalSpace.induced
      (fun x : Foundations.Scheme.AffineComplexPoints.affineComplexPoints A => (x : A → ℂ)) inferInstance
  apply Continuous.le_induced
  let : TopologicalSpace (Foundations.Scheme.AffineComplexPoints.affineComplexPoints A) :=
    TopologicalSpace.induced (Foundations.Scheme.AffineComplexPoints.affineComplexPoints.coordinates g) inferInstance
  apply continuous_pi
  intro a
  obtain ⟨p, rfl⟩ := Foundations.Scheme.AffineComplexPoints.affineComplexPoints.aeval_surjective_of_adjoin_eq_top g hg a
  change @Continuous (Foundations.Scheme.AffineComplexPoints.affineComplexPoints A) ℂ
    (TopologicalSpace.induced (Foundations.Scheme.AffineComplexPoints.affineComplexPoints.coordinates g) inferInstance) _
    (Foundations.Scheme.AffineComplexPoints.affineComplexPoints.eval (MvPolynomial.aeval g p))
  rw [Foundations.Scheme.AffineComplexPoints.affineComplexPoints.eval_aeval]
  exact (MvPolynomial.continuous_eval p).comp
    (continuous_induced_dom (f := Foundations.Scheme.AffineComplexPoints.affineComplexPoints.coordinates g))

/-- A point is determined by its values on any algebra generating family. -/
theorem Foundations.Scheme.AffineComplexPoints.affineComplexPoints.coordinates_injective (g : ι → A)
    (hg : Algebra.adjoin ℂ (Set.range g) = ⊤) :
    Function.Injective (Foundations.Scheme.AffineComplexPoints.affineComplexPoints.coordinates g) := by
  intro x y h
  apply AlgHom.ext_of_adjoin_eq_top hg
  rintro a ⟨i, rfl⟩
  exact congrFun h i

/-- Generating coordinates embed the complex-point space topologically. -/
theorem Foundations.Scheme.AffineComplexPoints.affineComplexPoints.isEmbedding_coordinates (g : ι → A)
    (hg : Algebra.adjoin ℂ (Set.range g) = ⊤) :
    Topology.IsEmbedding (Foundations.Scheme.AffineComplexPoints.affineComplexPoints.coordinates g) :=
  ⟨Foundations.Scheme.AffineComplexPoints.affineComplexPoints.isInducing_coordinates g hg, Foundations.Scheme.AffineComplexPoints.affineComplexPoints.coordinates_injective g hg⟩

/-- Continuity can be tested on the values of algebra generators alone. -/
theorem Foundations.Scheme.AffineComplexPoints.affineComplexPoints.continuous_iff_coordinates (g : ι → A)
    (hg : Algebra.adjoin ℂ (Set.range g) = ⊤)
    {X : Type z} [TopologicalSpace X] (f : X → Foundations.Scheme.AffineComplexPoints.affineComplexPoints A) :
    Continuous f ↔ ∀ i : ι, Continuous (fun x => f x (g i)) :=
  (Foundations.Scheme.AffineComplexPoints.affineComplexPoints.isInducing_coordinates g hg).continuous_iff.trans continuous_pi_iff

/-- Two algebra generating families define exactly the same topology. -/
theorem Foundations.Scheme.AffineComplexPoints.affineComplexPoints.induced_coordinates_eq (g : ι → A) (h : κ → A)
    (hg : Algebra.adjoin ℂ (Set.range g) = ⊤)
    (hh : Algebra.adjoin ℂ (Set.range h) = ⊤) :
    TopologicalSpace.induced (Foundations.Scheme.AffineComplexPoints.affineComplexPoints.coordinates g) inferInstance =
      TopologicalSpace.induced (Foundations.Scheme.AffineComplexPoints.affineComplexPoints.coordinates h) inferInstance :=
  (Foundations.Scheme.AffineComplexPoints.affineComplexPoints.isInducing_coordinates g hg).eq_induced.symm.trans
    (Foundations.Scheme.AffineComplexPoints.affineComplexPoints.isInducing_coordinates h hh).eq_induced

end OAI.AlgebraicGeometry

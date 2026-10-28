import OAI.AlgebraicGeometry.PELModuli.IntegralModel.Components
import OAI.AlgebraicTopology.Cohomology.Singular.Contractible
import OAI.AlgebraicGeometry.Betti.Scheme

/-! # Product -/

namespace OAI.AlgebraicGeometry.PELModuli.IntegralModel.Product

noncomputable section

/-!
Canonical restriction and projection maps for the Betti cohomology of a
product. Their splitting is proved from actual scheme morphisms and the
vanishing of positive-degree cohomology of a point. No product comparison
is assumed. ProductDimensions completes the degree-one isomorphism using
the proved Künneth dimension formula, finite-dimensionality, and connectedness.
-/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.MonObj
open _root_.CategoryTheory.CartesianMonoidalCategory

open OAI.AlgebraicGeometry.Betti.Scheme

abbrev bettiQ (X : Over Foundations.Scheme.ProjectiveSpace.complexBase) (n : ℕ) :=
  Betti.Scheme.schemeBetti (ModuleCat.of ℚ ℚ) X n

abbrev bettiPullbackQ {X Y : Over Foundations.Scheme.ProjectiveSpace.complexBase} (f : X ⟶ Y) (n : ℕ) :
    bettiQ Y n →ₗ[ℚ] bettiQ X n :=
  (Betti.Scheme.schemeBettiMap (ModuleCat.of ℚ ℚ) n f).hom

theorem bettiPullbackQ_comp {X Y Z : Over Foundations.Scheme.ProjectiveSpace.complexBase}
    (f : X ⟶ Y) (g : Y ⟶ Z) (n : ℕ) :
    bettiPullbackQ (f ≫ g) n = (bettiPullbackQ f n).comp (bettiPullbackQ g n) := by
  change ((Betti.Scheme.schemeBettiFunctor (ModuleCat.of ℚ ℚ) n).map (g.op ≫ f.op)).hom = _
  rw [Functor.map_comp]
  rfl

@[simp] theorem bettiPullbackQ_id (X : Over Foundations.Scheme.ProjectiveSpace.complexBase) (n : ℕ) :
    bettiPullbackQ (𝟙 X) n = LinearMap.id := by
  change ((Betti.Scheme.schemeBettiFunctor (ModuleCat.of ℚ ℚ) n).map (𝟙 (Opposite.op X))).hom = _
  rw [CategoryTheory.Functor.map_id]
  rfl

/-- The constant group-identity map has zero pullback in positive degree. -/
theorem bettiPullbackQ_one {X Y : Over Foundations.Scheme.ProjectiveSpace.complexBase} [MonObj Y]
    (n : ℕ) (hn : n ≠ 0) : bettiPullbackQ (1 : X ⟶ Y) n = 0 := by
  let pt := 𝟙_ (Over Foundations.Scheme.ProjectiveSpace.complexBase)
  have : Subsingleton (Betti.Scheme.schemePointSpace pt) :=
    inferInstanceAs (Subsingleton (Over.mk (𝟙 Foundations.Scheme.ProjectiveSpace.complexBase) ⟶ pt))
  let : Subsingleton (bettiQ pt n) := ModuleCat.subsingleton_of_isZero
    (AlgebraicTopology.Cohomology.Singular.Contractible.isZero_singularCohomology_of_totallyDisconnected
      (ModuleCat.of ℚ ℚ) (Betti.Scheme.schemePointSpace pt) n hn)
  rw [CategoryTheory.Hom.one_def, bettiPullbackQ_comp]
  ext x
  change bettiPullbackQ (toUnit X) n (bettiPullbackQ η[Y] n x) = 0
  rw [show bettiPullbackQ η[Y] n x = 0 from Subsingleton.elim _ _, map_zero]

namespace ProductBetti

variable {r : ℕ} (A : Fin r → CommGrp (Over Foundations.Scheme.ProjectiveSpace.complexBase))

abbrev scheme : Over Foundations.Scheme.ProjectiveSpace.complexBase := ∏ᶜ fun j => (A j).X

/-- The i-th axis inclusion uses the chosen group identities in other factors. -/
def axis (i : Fin r) : (A i).X ⟶ scheme A :=
  Pi.lift (fun j => if h : i = j then eqToHom (congrArg (fun k => (A k).X) h) else 1)

@[simp] theorem axis_self (i : Fin r) :
    axis A i ≫ Pi.π (fun j => (A j).X) i = 𝟙 (A i).X := by
  simp [axis]

theorem axis_ne (i j : Fin r) (h : i ≠ j) :
    axis A i ≫ Pi.π (fun k => (A k).X) j = 1 := by
  simp [axis, h]

def restriction (n : ℕ) :
    bettiQ (scheme A) n →ₗ[ℚ] (∀ j, bettiQ (A j).X n) :=
  LinearMap.pi (fun j => bettiPullbackQ (axis A j) n)

def projectionSum (n : ℕ) :
    (∀ j, bettiQ (A j).X n) →ₗ[ℚ] bettiQ (scheme A) n :=
  ∑ j : Fin r,
    (bettiPullbackQ (Pi.π (fun k => (A k).X) j) n).comp (LinearMap.proj j)

/-- Restriction to axes is split by the sum of actual projection pullbacks. -/
theorem restriction_projectionSum (n : ℕ) (hn : n ≠ 0) :
    (restriction A n).comp (projectionSum A n) = LinearMap.id := by
  apply LinearMap.ext
  intro x
  funext i
  change bettiPullbackQ (axis A i) n
    ((∑ j : Fin r,
      (bettiPullbackQ (Pi.π (fun k => (A k).X) j) n).comp (LinearMap.proj j)) x) = x i
  simp only [LinearMap.sum_apply, LinearMap.comp_apply, LinearMap.proj_apply, map_sum]
  rw [Finset.sum_eq_single i]
  · change ((bettiPullbackQ (axis A i) n).comp
      (bettiPullbackQ (Pi.π (fun k => (A k).X) i) n)) (x i) = x i
    rw [← bettiPullbackQ_comp, axis_self, bettiPullbackQ_id]
    rfl
  · intro j _ hji
    change ((bettiPullbackQ (axis A i) n).comp
      (bettiPullbackQ (Pi.π (fun k => (A k).X) j) n)) (x j) = 0
    rw [← bettiPullbackQ_comp, axis_ne A i j (Ne.symm hji), bettiPullbackQ_one n hn]
    rfl
  · simp

theorem restriction_surjective (n : ℕ) (hn : n ≠ 0) :
    Function.Surjective (restriction A n) := by
  intro x
  exact ⟨projectionSum A n x, LinearMap.congr_fun (restriction_projectionSum A n hn) x⟩

theorem projectionSum_injective (n : ℕ) (hn : n ≠ 0) :
    Function.Injective (projectionSum A n) := by
  apply Function.LeftInverse.injective (g := restriction A n)
  intro x
  exact LinearMap.congr_fun (restriction_projectionSum A n hn) x

end ProductBetti

end

end OAI.AlgebraicGeometry.PELModuli.IntegralModel.Product

import OAI.NumberTheory.ArithmeticGroups.Lattices.CoordinateIntegralVector
import OAI.NumberTheory.ArithmeticGroups.Lattices.AdeleCoordinateLattice

/-! # Exterior Action -/

namespace OAI.NumberTheory.ArithmeticGroups.Lattices.Archimedean.ExteriorAction.Construction

noncomputable section

/-! A continuous exterior-coordinate action of the product of all
archimedean special-linear groups, with a discrete invariant integral
coordinate module. -/

open scoped Classical _root_.NumberField
open _root_.NumberField

abbrev FullArchimedeanSL (k : Type) [Field k] (n : ℕ) :=
  (v : InfinitePlace k) → Algebraic.SL n v.Completion

def fullArchimedeanSLMap (k : Type) [Field k] (n : ℕ) :
    Algebraic.SL n k →* FullArchimedeanSL k n where
  toFun g v := Matrix.SpecialLinearGroup.map (algebraMap k v.Completion) g
  map_one' := by ext v i j; simp
  map_mul' g h := by ext v i j; simp

def fullArchimedeanIntegralSL (k : Type) [Field k] [NumberField k] (n : ℕ) :
    Subgroup (FullArchimedeanSL k n) :=
  ((fullArchimedeanSLMap k n).comp
    (Matrix.SpecialLinearGroup.map (algebraMap (𝓞 k) k))).range

def fullArchimedeanMatrixGroup {k : Type} [Field k] {n : ℕ}
    (G : Algebraic.MatrixAlgebraicGroup k n) : Subgroup (FullArchimedeanSL k n) where
  carrier := {g | ∀ v, g v ∈ G.subgroup v.Completion (algebraMap k v.Completion)}
  one_mem' v := (G.subgroup v.Completion (algebraMap k v.Completion)).one_mem
  mul_mem' hg hh v := (G.subgroup v.Completion (algebraMap k v.Completion)).mul_mem (hg v) (hh v)
  inv_mem' hg v := (G.subgroup v.Completion (algebraMap k v.Completion)).inv_mem (hg v)

@[instance_reducible] def archimedeanExteriorAction (k : Type) [Field k] (n d r : ℕ) :
    MulAction (FullArchimedeanSL k n) (AdeleCoordinateLattice.Construction.CoordinateAdeleSpace k (ExteriorCoordinates.Construction.BoundedExteriorIndices n d r)) where
  smul g x v := CoordinateRepresentation.Construction.boundedExteriorCoordinateRepresentation d r (g v) (x v)
  one_smul x := by
    funext v
    change CoordinateRepresentation.Construction.boundedExteriorCoordinateRepresentation d r 1 (x v) = x v
    rw [map_one]
    rfl
  mul_smul g h x := by
    funext v
    change CoordinateRepresentation.Construction.boundedExteriorCoordinateRepresentation d r (g v * h v) (x v) =
      CoordinateRepresentation.Construction.boundedExteriorCoordinateRepresentation d r (g v)
        (CoordinateRepresentation.Construction.boundedExteriorCoordinateRepresentation d r (h v) (x v))
    rw [map_mul]
    rfl

theorem continuous_exterior_atCompletion (k : Type) [Field k] (n d r : ℕ)
    (v : InfinitePlace k) :
    Continuous (fun a : Algebraic.SL n v.Completion × (ExteriorCoordinates.Construction.BoundedExteriorIndices n d r → v.Completion) =>
      CoordinateRepresentation.Construction.boundedExteriorCoordinateRepresentation d r a.1 a.2) :=
  CoordinateRepresentation.Construction.continuous_boundedExteriorCoordinateRepresentation (k := v.Completion) n d r

theorem continuous_archimedeanExterior_atPlace (k : Type) [Field k] (n d r : ℕ)
    (v : InfinitePlace k) :
    Continuous (fun a : FullArchimedeanSL k n × AdeleCoordinateLattice.Construction.CoordinateAdeleSpace k (ExteriorCoordinates.Construction.BoundedExteriorIndices n d r) =>
      CoordinateRepresentation.Construction.boundedExteriorCoordinateRepresentation d r (a.1 v) (a.2 v)) := by
  have hg : Continuous (fun a : FullArchimedeanSL k n × AdeleCoordinateLattice.Construction.CoordinateAdeleSpace k (ExteriorCoordinates.Construction.BoundedExteriorIndices n d r) =>
      a.1 v) := (continuous_apply v).comp continuous_fst
  have hx : Continuous (fun a : FullArchimedeanSL k n × AdeleCoordinateLattice.Construction.CoordinateAdeleSpace k (ExteriorCoordinates.Construction.BoundedExteriorIndices n d r) =>
      a.2 v) := (continuous_apply v).comp continuous_snd
  convert! (continuous_exterior_atCompletion k n d r v).comp (hg.prodMk hx) using 1

theorem continuous_archimedeanExterior_apply (k : Type) [Field k] (n d r : ℕ) :
    Continuous (fun a : FullArchimedeanSL k n × AdeleCoordinateLattice.Construction.CoordinateAdeleSpace k (ExteriorCoordinates.Construction.BoundedExteriorIndices n d r) =>
      fun v => CoordinateRepresentation.Construction.boundedExteriorCoordinateRepresentation d r (a.1 v) (a.2 v)) :=
  continuous_pi (continuous_archimedeanExterior_atPlace k n d r)

theorem continuous_archimedeanExteriorAction (k : Type) [Field k] (n d r : ℕ) :
    let := archimedeanExteriorAction k n d r
    ContinuousSMul (FullArchimedeanSL k n) (AdeleCoordinateLattice.Construction.CoordinateAdeleSpace k (ExteriorCoordinates.Construction.BoundedExteriorIndices n d r)) := by
  let := archimedeanExteriorAction k n d r
  exact ⟨continuous_archimedeanExterior_apply k n d r⟩

theorem archimedeanExteriorAction_diagonal
    {k : Type} [Field k] {n d r : ℕ} (g : Algebraic.SL n k) (x : ExteriorCoordinates.Construction.BoundedExteriorIndices n d r → k) :
    let := archimedeanExteriorAction k n d r
    fullArchimedeanSLMap k n g • AdeleCoordinateLattice.Construction.coordinateAdeleEmbedding k _ x =
      AdeleCoordinateLattice.Construction.coordinateAdeleEmbedding k _ (CoordinateRepresentation.Construction.boundedExteriorCoordinateRepresentation d r g x) := by
  let := archimedeanExteriorAction k n d r
  funext v
  exact CoordinateRepresentation.Construction.boundedExteriorCoordinateRepresentation_scalar_extension (K := v.Completion) g x

theorem archimedeanIntegralSL_preserves_exterior_lattice
    {k : Type} [Field k] [NumberField k] {n d r : ℕ} :
    let := archimedeanExteriorAction k n d r
    ∀ γ ∈ fullArchimedeanIntegralSL k n,
      ∀ y ∈ AdeleCoordinateLattice.Construction.coordinateAdeleLattice (CoordinateIntegralVector.Construction.integralExteriorCoordinateLattice (R := 𝓞 k) (k := k) n d r),
        γ • y ∈ AdeleCoordinateLattice.Construction.coordinateAdeleLattice (CoordinateIntegralVector.Construction.integralExteriorCoordinateLattice (R := 𝓞 k) (k := k) n d r) := by
  let := archimedeanExteriorAction k n d r
  change ∀ γ ∈ fullArchimedeanIntegralSL k n,
    ∀ y ∈ AdeleCoordinateLattice.Construction.coordinateAdeleLattice (CoordinateIntegralVector.Construction.integralExteriorCoordinateLattice (R := 𝓞 k) (k := k) n d r),
      γ • y ∈ AdeleCoordinateLattice.Construction.coordinateAdeleLattice (CoordinateIntegralVector.Construction.integralExteriorCoordinateLattice (R := 𝓞 k) (k := k) n d r)
  rintro γ ⟨A, rfl⟩ y ⟨x, hx, rfl⟩
  refine ⟨CoordinateRepresentation.Construction.boundedExteriorCoordinateRepresentation d r
    (Matrix.SpecialLinearGroup.map (algebraMap (𝓞 k) k) A) x,
      CoordinateIntegralVector.Construction.integralExteriorCoordinateLattice_action_mem A hx, ?_⟩
  exact (archimedeanExteriorAction_diagonal _ x).symm

end

end OAI.NumberTheory.ArithmeticGroups.Lattices.Archimedean.ExteriorAction.Construction

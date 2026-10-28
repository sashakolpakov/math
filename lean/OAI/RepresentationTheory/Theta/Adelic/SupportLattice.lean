import OAI.RepresentationTheory.Theta.Adelic.FiniteSchwartzBounds
import OAI.RepresentationTheory.Theta.Adelic.MinkowskiCoordinatesPosition

/-! # Support Lattice -/

namespace OAI.RepresentationTheory.Theta.Adelic.SupportLattice

noncomputable section

/-! Construct the actual support lattice and bounded lattice weight for
each finite Schwartz tensor in the rational theta sum. Every lattice
point comes from a unique rational position. -/

open scoped Classical _root_.NumberField BoundedContinuousFunction

open OAI.RepresentationTheory.Theta.Adelic.BallGeometryData OAI.RepresentationTheory.Theta.Adelic.DataTheta OAI.RepresentationTheory.Theta.Adelic.FiniteSchwartz OAI.RepresentationTheory.Theta.Adelic.Evaluation
open OAI.RepresentationTheory.Theta.Adelic.MinkowskiCoordinatesPosition OAI.RepresentationTheory.Theta.Adelic.FiniteSchwartzBounds

variable {F : Type} [Field F] [NumberField F] {d : F} {m : ℕ}
variable {H : (Matrix (Fin 3) (Fin 3) (Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic F d))ˣ}
variable {K : (Matrix (Fin m) (Fin m) (Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic F d))ˣ}
variable (A : BallGeometryData.BallArithmeticData F d m H K)

def supportScale (f : FiniteSchwartz.finiteSchwartz F (3 * m)) : F :=
  (FiniteSchwartzBounds.finiteSchwartz_support_lattice F (3 * m) f).choose

theorem supportScale_nonzero (f : FiniteSchwartz.finiteSchwartz F (3 * m)) : supportScale f ≠ 0 :=
  (FiniteSchwartzBounds.finiteSchwartz_support_lattice F (3 * m) f).choose_spec.1

def supportLattice (f : FiniteSchwartz.finiteSchwartz F (3 * m)) : Submodule ℤ (BallGeometryData.FrameIndex A → ℝ) :=
  MinkowskiCoordinatesPosition.coordinateSupportLattice A (supportScale f)

instance supportLatticeDiscrete (f : FiniteSchwartz.finiteSchwartz F (3 * m)) : DiscreteTopology (supportLattice A f) :=
  MinkowskiCoordinatesPosition.coordinateSupportLattice_discrete A _ (supportScale_nonzero f)

theorem supportLattice_rational (f : FiniteSchwartz.finiteSchwartz F (3 * m)) (l : supportLattice A f) :
    ∃ x : Weil.Local.FunctionsMetaplectic.Construction.Position F (3 * m), (fun i => (MinkowskiCoordinatesPosition.rationalPositionCoordinates A x i : ℝ)) = l.val :=
  MinkowskiCoordinatesPosition.coordinateSupportLattice_rational A _ (supportScale_nonzero f) l

theorem rationalWeight_support (f : FiniteSchwartz.finiteSchwartz F (3 * m)) (x : Weil.Local.FunctionsMetaplectic.Construction.Position F (3 * m))
    (hx : DataTheta.rationalWeight f x ≠ 0) :
    (fun i => (MinkowskiCoordinatesPosition.rationalPositionCoordinates A x i : ℝ)) ∈ supportLattice A f := by
  have hs := (FiniteSchwartzBounds.finiteSchwartz_support_lattice F (3 * m) f).choose_spec.2 x hx
  exact ⟨Weil.AdelicSplitting.ThetaTest.Construction.mixedRationalPosition F (3 * m) x, hs, MinkowskiCoordinatesPosition.mixedPositionCoordinates_rational A x⟩

theorem rationalPosition_real_injective :
    Function.Injective (fun x : Weil.Local.FunctionsMetaplectic.Construction.Position F (3 * m) => fun i => (MinkowskiCoordinatesPosition.rationalPositionCoordinates A x i : ℝ)) := by
  intro x y h
  apply (MinkowskiCoordinatesPosition.rationalPositionCoordinates A).injective
  funext i
  have hi : (MinkowskiCoordinatesPosition.rationalPositionCoordinates A x i : ℝ) = (MinkowskiCoordinatesPosition.rationalPositionCoordinates A y i : ℝ) := congrFun h i
  exact_mod_cast hi

def latticeRationalPoint (f : FiniteSchwartz.finiteSchwartz F (3 * m)) (l : supportLattice A f) : Weil.Local.FunctionsMetaplectic.Construction.Position F (3 * m) :=
  (supportLattice_rational A f l).choose

theorem latticeRationalPoint_spec (f : FiniteSchwartz.finiteSchwartz F (3 * m)) (l : supportLattice A f) :
    (fun i => (MinkowskiCoordinatesPosition.rationalPositionCoordinates A (latticeRationalPoint A f l) i : ℝ)) = l.val :=
  (supportLattice_rational A f l).choose_spec

theorem latticeRationalPoint_of_rational (f : FiniteSchwartz.finiteSchwartz F (3 * m)) (x : Weil.Local.FunctionsMetaplectic.Construction.Position F (3 * m))
    (hx : (fun i => (MinkowskiCoordinatesPosition.rationalPositionCoordinates A x i : ℝ)) ∈ supportLattice A f) :
    latticeRationalPoint A f ⟨fun i => (MinkowskiCoordinatesPosition.rationalPositionCoordinates A x i : ℝ), hx⟩ = x :=
  rationalPosition_real_injective A (latticeRationalPoint_spec A f _)

def latticeWeight (f : FiniteSchwartz.finiteSchwartz F (3 * m)) : supportLattice A f →ᵇ ℂ := by
  let C := (FiniteSchwartzBounds.finiteSchwartz_uniform_bound F (3 * m) f).choose
  have hC := (FiniteSchwartzBounds.finiteSchwartz_uniform_bound F (3 * m) f).choose_spec
  let w : supportLattice A f → ℂ := fun l => DataTheta.rationalWeight f (latticeRationalPoint A f l)
  refine BoundedContinuousFunction.mkOfBound ⟨w, continuous_of_discreteTopology⟩ (2 * C) ?_
  intro l t
  calc
    dist (w l) (w t) ≤ ‖w l‖ + ‖w t‖ := dist_le_norm_add_norm _ _
    _ ≤ C + C := add_le_add (hC _) (hC _)
    _ = 2 * C := by ring

theorem latticeWeight_apply (f : FiniteSchwartz.finiteSchwartz F (3 * m)) (l : supportLattice A f) :
    latticeWeight A f l = DataTheta.rationalWeight f (latticeRationalPoint A f l) := by
  unfold latticeWeight
  rfl

theorem latticeWeight_rational (f : FiniteSchwartz.finiteSchwartz F (3 * m)) (x : Weil.Local.FunctionsMetaplectic.Construction.Position F (3 * m))
    (hx : (fun i => (MinkowskiCoordinatesPosition.rationalPositionCoordinates A x i : ℝ)) ∈ supportLattice A f) :
    latticeWeight A f ⟨fun i => (MinkowskiCoordinatesPosition.rationalPositionCoordinates A x i : ℝ), hx⟩ = DataTheta.rationalWeight f x := by
  rw [latticeWeight_apply, latticeRationalPoint_of_rational]

end

end OAI.RepresentationTheory.Theta.Adelic.SupportLattice

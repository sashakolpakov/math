import OAI.ArithmeticGeometry.Models.SpreadingOut.Projective
import Mathlib.Algebra.Module.Submodule.Union
import Mathlib.AlgebraicGeometry.Morphisms.Affine
import Lean.Util.CollectAxioms

/-! # Neighborhoods -/

namespace OAI.AlgebraicGeometry.PELModuli.IntegralModel.Projective.Neighborhoods

noncomputable section

/-!
Finite subsets of a projective scheme over an infinite field have affine
neighborhoods. A linear homogeneous form avoiding every point is constructed
by avoiding finitely many proper vector subspaces. This supplies the affine
orbit neighborhoods needed in effective finite descent.
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry

open OAI.ArithmeticGeometry.Models.SpreadingOut.Projective.Construction.ProjectiveConstruction

universe u

variable {K : Type u} [Field K] [Infinite K]

theorem projective_finite_set_affine_neighborhood (n : ℕ)
    (F : Set (ArithmeticGeometry.Models.SpreadingOut.Projective.Construction.ProjectiveConstruction.projectiveSpace (K := K) n)) (hF : F.Finite) :
    ∃ U : (ArithmeticGeometry.Models.SpreadingOut.Projective.Construction.ProjectiveConstruction.projectiveSpace (K := K) n).Opens, IsAffineOpen U ∧ F ⊆ U := by
  classical
  let : Finite F := hF.to_subtype
  let V := ArithmeticGeometry.Models.SpreadingOut.Projective.Construction.ProjectiveConstruction.projectiveGrading (K := K) n 1
  let p (x : F) : Submodule K V :=
    ((x.val.asHomogeneousIdeal.toIdeal).restrictScalars K).comap
      (ArithmeticGeometry.Models.SpreadingOut.Projective.Construction.ProjectiveConstruction.projectiveGrading (K := K) n 1).subtype
  have hp (x : F) : p x ≠ ⊤ := by
    obtain ⟨i, hi⟩ := ArithmeticGeometry.Models.SpreadingOut.Projective.Construction.ProjectiveConstruction.exists_mem_projectiveCoordinateOpen n x.val
    have hn : MvPolynomial.X i ∉ x.val.asHomogeneousIdeal :=
      (ArithmeticGeometry.Models.SpreadingOut.Projective.Construction.ProjectiveConstruction.mem_projectiveCoordinateOpen n i x.val).mp hi
    intro htop
    let v : V := ⟨MvPolynomial.X i, MvPolynomial.isHomogeneous_X K i⟩
    have hv : v ∈ p x := htop ▸ Submodule.mem_top
    exact hn hv
  obtain ⟨l, hl⟩ := Submodule.exists_forall_notMem_of_forall_ne_top p hp
  refine ⟨Proj.basicOpen (ArithmeticGeometry.Models.SpreadingOut.Projective.Construction.ProjectiveConstruction.projectiveGrading (K := K) n) l.val,
    Proj.isAffineOpen_basicOpen _ _ l.property Nat.zero_lt_one, ?_⟩
  intro x hx
  apply (Proj.mem_basicOpen _ _ x).mpr
  exact hl ⟨x, hx⟩

/-- Pulling the affine hyperplane complement back along an actual closed
projective embedding gives the required affine neighborhood on the source. -/
theorem finite_set_affine_neighborhood_of_projective_embedding
    {X : Scheme.{u}} (n : ℕ) (i : X ⟶ ArithmeticGeometry.Models.SpreadingOut.Projective.Construction.ProjectiveConstruction.projectiveSpace (K := K) n)
    [IsClosedImmersion i] (F : Set X) (hF : F.Finite) :
    ∃ U : X.Opens, IsAffineOpen U ∧ F ⊆ U := by
  obtain ⟨V, hV, hFV⟩ := projective_finite_set_affine_neighborhood n (i '' F) (hF.image i)
  exact ⟨i ⁻¹ᵁ V, hV.preimage i, fun x hx ↦ hFV ⟨x, hx, rfl⟩⟩

end

end OAI.AlgebraicGeometry.PELModuli.IntegralModel.Projective.Neighborhoods

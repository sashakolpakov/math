import OAI.Geometry.ComplexTorus.RiemannProjectivity.HolomorphicContourF
import OAI.Geometry.ComplexTorus.RiemannProjectivity.FiniteBranchesAt
import Mathlib.Analysis.Calculus.Implicit

/-! # Submersion Coordinates Exists -/

namespace OAI.Geometry.ComplexTorus.RiemannProjectivity.SubmersionCoordinatesExists.Constructions.SubmersionCoordinates

noncomputable section

/-! # RiemannProjectivity: holomorphic coordinates for a submersion -/

open Set
open scoped _root_.Topology ContDiff

variable {V R : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V] [FiniteDimensional ℂ V]
  [NormedAddCommGroup R] [NormedSpace ℂ R] [FiniteDimensional ℂ R]

theorem exists_coordinates {G : V → R} {U : Set V} (hU : IsOpen U)
    (hG : DifferentiableOn ℂ G U) {x : V} (hx : x ∈ U)
    (d : V →L[ℂ] R) (hder : HasFDerivAt G d x) (hd : Function.Surjective d) :
    ∃ q : OpenPartialHomeomorph V (R × d.ker), x ∈ q.source ∧ q.source ⊆ U ∧
      (∀ v, (q v).1 = G v) ∧ DifferentiableOn ℂ q.symm q.target := by
  let : CompleteSpace V := FiniteDimensional.complete ℂ V
  let : CompleteSpace R := FiniteDimensional.complete ℂ R
  have hs := (HolomorphicRegularityAt.Constructions.HolomorphicRegularity.contDiffAt_one_of_differentiableOn hU hG hx).hasStrictFDerivAt
    (by norm_num)
  rw [hder.fderiv] at hs
  let hk := d.ker_closedComplemented_of_finiteDimensional_range
  let φ := hs.implicitFunctionDataOfComplemented G d (LinearMap.range_eq_top.mpr hd) hk
  have hφ : DifferentiableOn ℂ φ.prodFun U := hG.prodMk
    (((Classical.choose hk).differentiable.comp (differentiable_id.sub_const x)).differentiableOn)
  have hφbij : Function.Bijective (fderiv ℂ φ.prodFun x) := by
    change Function.Bijective (fderiv ℂ φ.prodFun φ.pt)
    rw [φ.hasStrictFDerivAt.hasFDerivAt.fderiv]
    exact (φ.leftDeriv.equivProdOfSurjectiveOfIsCompl φ.rightDeriv
      φ.range_leftDeriv φ.range_rightDeriv φ.isCompl_ker).bijective
  obtain ⟨q, hqx, hqφ, hqi⟩ := FiniteBranchesAt.Constructions.FiniteBranches.holomorphic_local_inverse hU hφ hx hφbij
  refine ⟨q.restrOpen U hU, ⟨hqx, hx⟩, fun _ hz => hz.2, ?_, hqi.mono (fun _ hz => hz.1)⟩
  intro v
  change (q v).1 = G v
  rw [congrFun hqφ v]
  rfl

end

end OAI.Geometry.ComplexTorus.RiemannProjectivity.SubmersionCoordinatesExists.Constructions.SubmersionCoordinates

import OAI.Geometry.ComplexTorus.RiemannProjectivity.FiniteRank
import OAI.Geometry.ComplexTorus.RiemannProjectivity.SubmersionCoordinatesExists

/-! # Finite Submersion -/

namespace OAI.Geometry.ComplexTorus.RiemannProjectivity.FiniteSubmersion.Constructions.FiniteSubmersionFiber

noncomputable section

/-! # RiemannProjectivity: a finite fiber removes the kernel of a projected submersion -/

open Set Filter _root_.Module
open scoped _root_.Topology

variable {V W R : Type*}
  [NormedAddCommGroup V] [NormedSpace ℂ V] [FiniteDimensional ℂ V]
  [NormedAddCommGroup W] [NormedSpace ℂ W] [FiniteDimensional ℂ W]
  [NormedAddCommGroup R] [NormedSpace ℂ R] [FiniteDimensional ℂ R]

omit [FiniteDimensional ℂ W] in
theorem subsingleton_kernel {F : V → W} {U : Set V}
    (hU : IsOpen U) (hF : DifferentiableOn ℂ F U) {x : V} (hx : x ∈ U)
    (Q : W →L[ℂ] R) (d : V →L[ℂ] R)
    (hGder : HasFDerivAt (fun z => Q (F z)) d x) (hd : Function.Surjective d)
    (hmax : ∀ z ∈ U, finrank ℂ (fderiv ℂ F z).range ≤ finrank ℂ R)
    (hfinite : {z : V | z ∈ U ∧ F z = F x}.Finite) : Subsingleton d.ker := by
  let G : V → R := fun z => Q (F z)
  have hG : DifferentiableOn ℂ G U := Q.differentiable.comp_differentiableOn hF
  obtain ⟨q', hqx', hQU, hfirstq, hqi⟩ :=
    SubmersionCoordinatesExists.Constructions.SubmersionCoordinates.exists_coordinates hU hG hx d hGder hd
  let H : R × d.ker → W := F ∘ q'.symm
  have hmap : MapsTo q'.symm q'.target U := fun z hz => hQU (q'.map_target hz)
  have hH : DifferentiableOn ℂ H q'.target :=
    hF.comp hqi hmap
  have hfirst : ∀ z ∈ q'.target, Q (H z) = z.1 := by
    intro z hz
    have h := congrArg Prod.fst (q'.right_inv hz)
    rw [hfirstq] at h
    exact h
  have hrank : ∀ z ∈ q'.target, finrank ℂ (fderiv ℂ H z).range ≤ finrank ℂ R := by
    intro z hz
    have hFi := hF.differentiableAt (hU.mem_nhds (hmap hz))
    have hqid := (hqi z hz).differentiableAt (q'.open_target.mem_nhds hz)
    have he : fderiv ℂ H z = (fderiv ℂ F (q'.symm z)).comp (fderiv ℂ q'.symm z) :=
      fderiv_comp z hFi hqid
    rw [he]
    have hle : ((fderiv ℂ F (q'.symm z)).comp (fderiv ℂ q'.symm z)).range ≤
        (fderiv ℂ F (q'.symm z)).range := by
      rintro _ ⟨v, rfl⟩
      exact ⟨fderiv ℂ q'.symm z v, rfl⟩
    exact (Submodule.finrank_mono hle).trans (hmax _ (hmap hz))
  have hHp : H (q' x) = F x := by
    change F (q'.symm (q' x)) = F x
    rw [q'.left_inv hqx']
  have hHfinite : {z : R × d.ker | z ∈ q'.target ∧ H z = H (q' x)}.Finite := by
    have himage : (q'.symm '' {z : R × d.ker | z ∈ q'.target ∧ H z = H (q' x)}).Finite := by
      apply hfinite.subset
      rintro _ ⟨z, hz, rfl⟩
      exact ⟨hmap hz.1, hz.2.trans hHp⟩
    exact himage.of_finite_image (q'.symm.injOn.mono (fun _ hz => hz.1))
  exact FiniteRank.Constructions.FiniteRankChart.subsingleton_vertical_of_finite_fiber
    q'.open_target hH Q hfirst hrank (q'.map_source hqx') hHfinite

end

end OAI.Geometry.ComplexTorus.RiemannProjectivity.FiniteSubmersion.Constructions.FiniteSubmersionFiber

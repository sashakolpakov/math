import OAI.AlgebraicGeometry.Resolution.Blowups.DualFrameBlowupSmooth

/-! # Dual Pair Blowup Smooth -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups.DualPairBlowupSmooth.Construction

noncomputable section

/-! Smoothness of an actual two-equation blowup with a dual derivation pair. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

variable {k R : Type u} [CommRing k] [CommRing R] [Algebra k R] [Algebra.Smooth k R]

/-- Two equations with dual derivations generate an actual center whose
entire blowup remains smooth over the original base. -/
theorem dual_pair_blowup_smooth (z g : R) (D E : Derivation k R R)
    (hDz : D z = 1) (hDg : D g = 0) (hEz : E z = 0) (hEg : E g = 1) :
    Smooth (ReesGrading.Construction.affineBlowupToSpec (Ideal.span {z, g}) ≫
      Spec.map (CommRingCat.ofHom (algebraMap k R))) := by
  let v : ULift.{u} Bool → R := fun i => if i.down then g else z
  let F : ULift.{u} Bool → Derivation k R R := fun i => if i.down then E else D
  have hF : ∀ i j, F i (v j) = if i = j then 1 else 0 := by
    rintro ⟨i⟩ ⟨j⟩
    cases i <;> cases j <;> simp [v, F, hDz, hDg, hEz, hEg]
  have hv : Set.range v = {z, g} := by
    ext x
    constructor
    · rintro ⟨⟨i⟩, rfl⟩
      cases i <;> simp [v]
    · intro hx
      rcases Set.mem_insert_iff.mp hx with rfl | hx
      · exact ⟨⟨false⟩, rfl⟩
      · have he : x = g := Set.mem_singleton_iff.mp hx
        exact ⟨⟨true⟩, he.symm⟩
  have h := DualFrameBlowupSmooth.Construction.dual_derivation_family_blowup_smooth v F hF
  rwa [hv] at h

end

end OAI.AlgebraicGeometry.Resolution.Blowups.DualPairBlowupSmooth.Construction

import OAI.AlgebraicGeometry.FormalGeometry.Completion.Endomorphism.Action

/-! # Group Law Cohomology -/

namespace OAI.AlgebraicGeometry.FormalGeometry.Completion.GroupLawCohomology.Construction

noncomputable section

/-!
# Completion: the group-law formula controlling H¹ additivity

All maps below are the already constructed pullbacks on geometric H¹.
The group-law defect is not asserted to vanish. Its kernel consists of
the actual classes primitive under the group law.
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj

universe u

variable (ℓ : ℕ) [Fact ℓ.Prime] (k : Type u) [Field k]
    (A : Over (Spec (CommRingCat.of k))) [GrpObj A] [IsCommMonObj A]

/-- The difference between group-law pullback and the sum of projection pullbacks. -/
def geometricH1GroupLawDefect :
    Cohomology.Construction.GeometricH1 ℓ A →ₗ[AlgebraicClosure ℚ_[ℓ]] Cohomology.Construction.GeometricH1 ℓ (A ⊗ A) :=
  Endomorphism.Action.Construction.geometricH1Pullback ℓ k μ[A] -
    (Endomorphism.Action.Construction.geometricH1Pullback ℓ k (fst A A) + Endomorphism.Action.Construction.geometricH1Pullback ℓ k (snd A A))

theorem algebraicEnd_add_apply (f g : Endomorphisms.Construction.AlgebraicEnd A) :
    (f + g).toMul.hom.hom = lift f.toMul.hom.hom g.toMul.hom.hom ≫ μ[A] := rfl

/-- Failure of endomorphism additivity factors through the group-law defect. -/
theorem geometricH1Pullback_add_defect (f g : Endomorphisms.Construction.AlgebraicEnd A) :
    Endomorphism.Action.Construction.geometricH1Pullback ℓ k (f + g).toMul.hom.hom -
        (Endomorphism.Action.Construction.geometricH1Pullback ℓ k f.toMul.hom.hom +
          Endomorphism.Action.Construction.geometricH1Pullback ℓ k g.toMul.hom.hom) =
      (Endomorphism.Action.Construction.geometricH1Pullback ℓ k (lift f.toMul.hom.hom g.toMul.hom.hom)).comp
        (geometricH1GroupLawDefect ℓ k A) := by
  rw [geometricH1GroupLawDefect, LinearMap.comp_sub, LinearMap.comp_add]
  simp only [← Endomorphism.Action.Construction.geometricH1Pullback_comp, lift_fst, lift_snd, algebraicEnd_add_apply]

variable {A} {B : Over (Spec (CommRingCat.of k))} [GrpObj B] [IsCommMonObj B]

omit [IsCommMonObj A] [IsCommMonObj B] in
/-- The group-law defect is natural for actual group-scheme homomorphisms. -/
theorem geometricH1GroupLawDefect_naturality (f : A ⟶ B) [IsMonHom f] :
    (geometricH1GroupLawDefect ℓ k A).comp (Endomorphism.Action.Construction.geometricH1Pullback ℓ k f) =
      (Endomorphism.Action.Construction.geometricH1Pullback ℓ k (f ⊗ₘ f)).comp (geometricH1GroupLawDefect ℓ k B) := by
  simp only [geometricH1GroupLawDefect, LinearMap.sub_comp, LinearMap.add_comp,
    LinearMap.comp_sub, LinearMap.comp_add, ← Endomorphism.Action.Construction.geometricH1Pullback_comp,
    IsMonHom.mul_hom, tensorHom_fst, tensorHom_snd]

variable (A)

/-- Primitive classes in the genuine geometric H¹; no equality with all H¹ is assumed. -/
abbrev PrimitiveGeometricH1 := LinearMap.ker (geometricH1GroupLawDefect ℓ k A)

/-- Addition of algebraic endomorphisms acts additively on each primitive class. -/
theorem geometricH1Pullback_add_on_primitive (f g : Endomorphisms.Construction.AlgebraicEnd A)
    (x : PrimitiveGeometricH1 ℓ k A) :
    Endomorphism.Action.Construction.geometricH1Pullback ℓ k (f + g).toMul.hom.hom x.val =
      Endomorphism.Action.Construction.geometricH1Pullback ℓ k f.toMul.hom.hom x.val +
        Endomorphism.Action.Construction.geometricH1Pullback ℓ k g.toMul.hom.hom x.val := by
  have h := congrArg (fun F => F x.val) (geometricH1Pullback_add_defect ℓ k A f g)
  have hx : geometricH1GroupLawDefect ℓ k A x.val = 0 := x.property
  simpa only [LinearMap.sub_apply, LinearMap.add_apply, LinearMap.comp_apply, hx,
    map_zero, sub_eq_zero] using h

end

end OAI.AlgebraicGeometry.FormalGeometry.Completion.GroupLawCohomology.Construction

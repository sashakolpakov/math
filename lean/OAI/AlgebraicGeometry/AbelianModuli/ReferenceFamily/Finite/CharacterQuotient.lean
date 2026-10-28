import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.UnramifiedCharacterQuotient
import Mathlib.RingTheory.Spectrum.Prime.FreeLocus

/-! # Character Quotient -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Finite.CharacterQuotient

noncomputable section

/-! A finite algebra basis gives exactly the full character quotient.
The constructed splitting proves projectivity and local constancy of
its fiber rank, including over nonreduced coefficient rings. -/

variable {R B V I : Type} [CommRing R] [CommRing B] [Algebra R B]
  [AddCommGroup V] [Module R V]

theorem iSup_range_eq_basis_range [Fintype I] (b : Module.Basis I R B)
    (f : B →ₗ[R] Module.End R V) :
    (⨆ a : B, (f a).range) = ⨆ i : I, (f (b i)).range := by
  apply le_antisymm
  · apply iSup_le
    intro a v hv
    obtain ⟨w, rfl⟩ := hv
    have hfa : f a = ∑ i, (b.repr a) i • f (b i) := by
      conv_lhs => rw [← b.sum_repr a]
      simp only [map_sum, map_smul]
    rw [hfa, LinearMap.sum_apply]
    apply Submodule.sum_mem
    intro i _
    exact Submodule.smul_mem _ _ (le_iSup (fun j => (f (b j)).range) i
      (LinearMap.mem_range_self (f (b i)) w))
  · exact iSup_le (fun i => le_iSup (fun a : B => (f a).range) (b i))

variable [Module B V] [IsScalarTower R B V]

theorem characterActionRelations_eq_basis [Fintype I] (b : Module.Basis I R B)
    (χ : B →ₐ[R] R) :
    UnramifiedCharacterQuotient.characterActionRelations (V := V) χ =
      PELModuli.IntegralModel.ConormalEigenquotient.conormalEigenRelations (fun i => (Algebra.lsmul R R V) (b i)) (fun i => χ (b i)) := by
  let f : B →ₗ[R] Module.End R V :=
    (Algebra.lsmul R R V : B →ₐ[R] Module.End R V).toLinearMap -
      (LinearMap.lsmul R V).comp χ.toLinearMap
  exact iSup_range_eq_basis_range b f

variable [Algebra.FormallyUnramified R B] [Algebra.EssFiniteType R B]

theorem finiteCharacterQuotient_projective [Fintype I] [Module.Projective R V]
    (b : Module.Basis I R B) (χ : B →ₐ[R] R) :
    Module.Projective R
      (PELModuli.IntegralModel.ConormalEigenquotient.conormalEigenquotient (fun i => (Algebra.lsmul R R V) (b i)) (fun i => χ (b i))) := by
  change Module.Projective R (V ⧸ PELModuli.IntegralModel.ConormalEigenquotient.conormalEigenRelations
    (fun i => (Algebra.lsmul R R V) (b i)) (fun i => χ (b i)))
  rw [← characterActionRelations_eq_basis b χ]
  exact UnramifiedCharacterQuotient.characterQuotient_projective χ

theorem finiteCharacterQuotient_rank_isLocallyConstant
    [Fintype I] [Module.Projective R V] [Module.Finite R V] [IsNoetherianRing R]
    (b : Module.Basis I R B) (χ : B →ₐ[R] R) :
    IsLocallyConstant (Module.rankAtStalk (R := R)
      (PELModuli.IntegralModel.ConormalEigenquotient.conormalEigenquotient (fun i => (Algebra.lsmul R R V) (b i)) (fun i => χ (b i)))) := by
  let : Module.Projective R
      (PELModuli.IntegralModel.ConormalEigenquotient.conormalEigenquotient (fun i => (Algebra.lsmul R R V) (b i)) (fun i => χ (b i))) :=
    finiteCharacterQuotient_projective b χ
  let : Module.FinitePresentation R
      (PELModuli.IntegralModel.ConormalEigenquotient.conormalEigenquotient (fun i => (Algebra.lsmul R R V) (b i)) (fun i => χ (b i))) :=
    PELModuli.IntegralModel.ConormalEigenquotient.conormalEigenquotient_finitePresentation _ _
  exact Module.isLocallyConstant_rankAtStalk

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Finite.CharacterQuotient

import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Finite.HomologySequences

/-! # Cohomology Representatives -/

namespace OAI.AlgebraicGeometry.HilbertScheme.Presentations.Finite.CohomologyRepresentatives

noncomputable section

/-! A finite submodule containing representatives modulo boundaries gives finite actual module homology. -/

open _root_.CategoryTheory

universe u v w

variable (R : Type u) [CommRing R] [IsNoetherianRing R]

theorem finite_comap_of_injective
    {M : Type v} [AddCommGroup M] [Module R M]
    {N : Type w} [AddCommGroup N] [Module R N]
    (f : M →ₗ[R] N) (hf : Function.Injective f) (U : Submodule R N) [Module.Finite R U] :
    Module.Finite R (U.comap f) := by
  let j : U.comap f →ₗ[R] U := (f.comp (U.comap f).subtype).codRestrict U (fun x => x.property)
  apply Module.Finite.of_injective j
  intro x y hxy
  apply Subtype.ext
  exact hf (congrArg Subtype.val hxy)

theorem finite_shortComplex_homology_of_representatives
    (S : ShortComplex (ModuleCat.{v} R)) (U : Submodule R S.X₂) [Module.Finite R U]
    (hrep : ∀ b : S.X₂, S.g b = 0 → ∃ a : S.X₁, b - S.f a ∈ U) :
    Module.Finite R S.homology := by
  let T := U.comap S.g.hom.ker.subtype
  let : Module.Finite R T := finite_comap_of_injective R S.g.hom.ker.subtype
    (Submodule.subtype_injective _) U
  let π : T →ₗ[R] (S.g.hom.ker ⧸ S.moduleCatToCycles.range) :=
    S.moduleCatToCycles.range.mkQ.comp T.subtype
  have hπ : Function.Surjective π := by
    intro x
    obtain ⟨b, rfl⟩ := Submodule.Quotient.mk_surjective S.moduleCatToCycles.range x
    obtain ⟨a, ha⟩ := hrep b.val b.property
    let c : S.g.hom.ker := ⟨b.val - S.f a, by
      change S.g.hom (b.val - S.f a) = 0
      rw [map_sub, b.property, S.moduleCat_zero_apply, sub_self]⟩
    refine ⟨⟨c, ha⟩, ?_⟩
    change S.moduleCatToCycles.range.mkQ c = S.moduleCatToCycles.range.mkQ b
    apply (Submodule.Quotient.eq _).mpr
    refine ⟨-a, ?_⟩
    apply Subtype.ext
    change S.f.hom (-a) = (b.val - S.f a) - b.val
    rw [map_neg]
    abel
  let : Module.Finite R (S.g.hom.ker ⧸ S.moduleCatToCycles.range) := Module.Finite.of_surjective π hπ
  let : Module.Finite R S.moduleCatLeftHomologyData.H :=
    inferInstanceAs (Module.Finite R (S.g.hom.ker ⧸ S.moduleCatToCycles.range))
  exact Module.Finite.of_surjective S.moduleCatHomologyIso.inv.hom
    ((ModuleCat.epi_iff_surjective _).mp inferInstance)

end

end OAI.AlgebraicGeometry.HilbertScheme.Presentations.Finite.CohomologyRepresentatives

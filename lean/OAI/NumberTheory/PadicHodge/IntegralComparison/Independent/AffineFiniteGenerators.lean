import OAI.NumberTheory.PadicHodge.IntegralComparison.Independent.AffineSections
import OAI.NumberTheory.PadicHodge.IntegralComparison.Independent.AffineKernels

/-! # Affine Finite Generators -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Independent.AffineFiniteGenerators

noncomputable section

open _root_.CategoryTheory Limits _root_.AlgebraicGeometry

universe u

variable (R : CommRingCat.{u}) (M : (Spec R).Modules)

theorem generators [M.IsQuasicoherent]
    [Module.Finite R ((moduleSpecΓFunctor (R := R)).obj M)] :
    ∃ G : M.GeneratingSections, G.IsFiniteType := by
  let V := (moduleSpecΓFunctor (R := R)).obj M
  obtain ⟨r, s, hs⟩ := Module.Finite.exists_fin (R := R) (M := V)
  let ι := ULift.{u} (Fin r)
  let v : ι → V := fun i => s i.down
  have hv : Submodule.span R (Set.range v) = ⊤ := by
    have hr : Set.range v = Set.range s := by
      ext x
      constructor
      · rintro ⟨i, rfl⟩
        exact ⟨i.down, rfl⟩
      · rintro ⟨i, rfl⟩
        exact ⟨ULift.up i, rfl⟩
    rw [hr, hs]
  let f : ModuleCat.of R (ι →₀ R) ⟶ V :=
    ModuleCat.ofHom (X := ModuleCat.of R (ι →₀ R)) (Y := V)
      (Finsupp.linearCombination (M := V) R v)
  let : Epi f := (ModuleCat.epi_iff_surjective f).mpr
    ((span_range_eq_top_iff_surjective_finsuppLinearCombination R).mp hv)
  let : (tilde.functor R).PreservesEpimorphisms :=
    Functor.preservesEpimorphisms_of_adjunction tilde.adjunction
  let e := tildeFinsupp (R := R) ι
  let g : SheafOfModules.free (R := (Spec R).ringCatSheaf) ι ⟶ M :=
    e.inv ≫ (tilde.functor R).map f ≫ M.fromTildeΓ
  let : Epi g := by
    let : IsIso e.inv := e.isIso_inv
    have hf : Epi ((tilde.functor R).map f) := Functor.map_epi _ f
    exact epi_comp' (IsIso.epi_of_iso e.inv)
      (epi_comp' hf (IsIso.epi_of_iso M.fromTildeΓ))
  let G : M.GeneratingSections :=
    { I := ι
      s := M.freeHomEquiv g
      epi := by rw [Equiv.symm_apply_apply]; infer_instance }
  exact ⟨G, ⟨inferInstanceAs (Finite ι)⟩⟩

theorem finiteType [M.IsQuasicoherent]
    [Module.Finite R ((moduleSpecΓFunctor (R := R)).obj M)] : M.IsFiniteType := by
  obtain ⟨G, hG⟩ := generators R M
  let : G.IsFiniteType := hG
  refine { exists_localGeneratorsData := ?_ }
  refine ⟨G.localGeneratorsData, ?_⟩
  constructor
  intro U
  exact ⟨hG.finite⟩

theorem finite_of_generators [M.IsQuasicoherent] (G : M.GeneratingSections) [G.IsFiniteType] :
    Module.Finite R ((moduleSpecΓFunctor (R := R)).obj M) := by
  let : Finite G.I := (inferInstance : G.IsFiniteType).finite
  let : Module.Finite R (ModuleCat.of R (G.I →₀ R)) := by
    change Module.Finite R (G.I →₀ R)
    infer_instance
  let F := moduleSpecΓFunctor (R := R)
  let P : (Spec R).Modules := SheafOfModules.free G.I
  let e := tildeFinsupp (R := R) G.I
  let : P.IsQuasicoherent :=
    (SheafOfModules.isQuasicoherent (Spec R).ringCatSheaf).prop_of_iso e inferInstance
  let eΓ : ModuleCat.of R (G.I →₀ R) ≅ F.obj P :=
    tilde.isoTop (R := R) (ModuleCat.of R (G.I →₀ R)) ≪≫ F.mapIso e
  let : Module.Finite R (F.obj P) := Module.Finite.equiv eΓ.toLinearEquiv
  have hepi : Epi (F.map G.π) :=
    @AffineSections.gamma_map_epi R P M inferInstance inferInstance G.π G.epi
  exact Module.Finite.of_surjective (F.map G.π).hom
    ((ModuleCat.epi_iff_surjective _).mp hepi)

theorem kernel_sections_finite [IsNoetherianRing R]
    [Module.Finite R ((moduleSpecΓFunctor (R := R)).obj M)]
    {N : (Spec R).Modules} (f : M ⟶ N) :
    Module.Finite R ((moduleSpecΓFunctor (R := R)).obj (kernel f)) := by
  let F := AffineKernels.sections R ⊤
  let : PreservesLimit (parallelPair f 0) F := AffineKernels.preservesKernel R ⊤ f
  let e := KernelLocalizationTransport.kernelIso f F
  let : Module.Finite R (F.obj M) := by
    change Module.Finite R ((moduleSpecΓFunctor (R := R)).obj M)
    infer_instance
  let : IsNoetherian R (F.obj M) := isNoetherian_of_isNoetherianRing_of_finite R (F.obj M)
  let : Module.Finite R (F.map f).hom.ker :=
    Module.Finite.of_injective (F.map f).hom.ker.subtype Subtype.val_injective
  exact Module.Finite.equiv e.symm.toLinearEquiv

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Independent.AffineFiniteGenerators

import OAI.AlgebraicGeometry.Divisors.LineBundles.LineBundle.MorphismCoordinate
import OAI.AlgebraicGeometry.Divisors.LineBundles.Scheme.ModuleBasisIso

/-! # Surjective Iso -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.LineBundle.SurjectiveIso.Cycles

noncomputable section

/-! A surjective morphism of actual line bundles is locally
multiplication by a unit, and hence is a sheaf isomorphism. -/

open _root_.AlgebraicGeometry _root_.CategoryTheory _root_.TopologicalSpace

theorem rankOneLinearMap_bijective_of_surjective {R : Type*} [CommRing R]
    (φ : R →ₗ[R] R) (hφ : Function.Surjective φ) : Function.Bijective φ := by
  have hm (r : R) : φ r = r * φ 1 := by
    simpa only [smul_eq_mul, mul_one] using φ.map_smul r 1
  obtain ⟨r, hr⟩ := hφ 1
  have hru : r * φ 1 = 1 := (hm r).symm.trans hr
  let u : Rˣ := ⟨φ 1, r, (mul_comm _ _).trans hru, hru⟩
  have he : (φ : R → R) = fun a => a * u.val := funext hm
  rw [he]
  exact IsUnit.isUnit_iff_mulRight_bijective.mp u.isUnit

theorem lineBundleMorphism_isIso_of_basis_surjective {X : Scheme.{0}}
    (L M : LineBundles.Scheme.SchemeIdealModule.BundleCycles.SchemeLineBundle X) (φ : L.sheaf ⟶ M.sheaf)
    (B₀ : Set X.Opens) (hB₀ : Opens.IsBasis B₀)
    (hφ : ∀ U ∈ B₀, Function.Surjective (φ.app U)) : IsIso φ := by
  let B : Set X.Opens := {W | W ∈ B₀ ∧ ∃ x : X,
    W ≤ L.trivializingOpen x ∧ W ≤ M.trivializingOpen x}
  have hB : Opens.IsBasis B := by
    apply Opens.isBasis_iff_nbhd.mpr
    intro U x hx
    obtain ⟨W, hW, hxW, hWU⟩ := Opens.isBasis_iff_nbhd.mp hB₀
      (show x ∈ (U ⊓ L.trivializingOpen x) ⊓ M.trivializingOpen x from
        ⟨⟨hx, L.mem_trivializingOpen x⟩, M.mem_trivializingOpen x⟩)
    exact ⟨W, ⟨hW, x, hWU.trans (inf_le_left.trans inf_le_right), hWU.trans inf_le_right⟩,
      hxW, hWU.trans (inf_le_left.trans inf_le_left)⟩
  apply LineBundles.Scheme.ModuleBasisIso.BundleCycles.schemeModule_isIso_of_basis φ hB
  rintro W ⟨hW, x, hL, hM⟩
  let eL := L.sectionFrame x W hL
  let eM := M.sectionFrame x W hM
  let θ := eM.toLinearMap.comp ((MorphismCoordinate.Cycles.moduleSectionLinearMap φ W).comp eL.symm.toLinearMap)
  have hθ : Function.Surjective θ := eM.surjective.comp ((hφ W hW).comp eL.symm.surjective)
  refine ⟨?_, hφ W hW⟩
  intro s t hst
  apply eL.injective
  apply (rankOneLinearMap_bijective_of_surjective θ hθ).injective
  change eM (φ.app W (eL.symm (eL s))) = eM (φ.app W (eL.symm (eL t)))
  rw [eL.symm_apply_apply, eL.symm_apply_apply, hst]

theorem lineBundleMorphism_isIso_of_affine_surjective {X : Scheme.{0}}
    (L M : LineBundles.Scheme.SchemeIdealModule.BundleCycles.SchemeLineBundle X) (φ : L.sheaf ⟶ M.sheaf)
    (hφ : ∀ U : X.affineOpens, Function.Surjective (φ.app U.1)) : IsIso φ := by
  exact lineBundleMorphism_isIso_of_basis_surjective L M φ _ X.isBasis_affineOpens
    (fun U hU => hφ ⟨U, hU⟩)

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.LineBundle.SurjectiveIso.Cycles

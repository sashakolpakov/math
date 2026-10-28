import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Abelian.AffineBaseChangeFunctions
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.CartesianOpenBasePullback
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.FunctionSheafAffineCriterion
import Mathlib.AlgebraicGeometry.Noetherian

/-! # Base Change Function Sheaf -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Abelian.BaseChangeFunctionSheaf

noncomputable section

section

/-! The function pullback is an isomorphism on every affine test open
whose coefficient map lies in an affine open of a locally noetherian base. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

theorem abelian_baseChange_function_app_of_affine_pair
    {S : Scheme.{0}} [IsLocallyNoetherian S] {g : ℕ} (A : HilbertConstruction.Abelian.Schemes.AbelianScheme g S)
    {Y T : Scheme.{0}} (a : Y ⟶ A.scheme.left) (ρ : Y ⟶ T) (t : T ⟶ S)
    (hp : IsPullback a ρ A.scheme.hom t)
    (U : S.Opens) (hU : IsAffineOpen U) (V : T.Opens) (hV : IsAffineOpen V)
    (hVU : V ≤ t ⁻¹ᵁ U) : IsIso (ρ.app V) := by
  let : IsAffine U.toScheme := hU
  let : IsAffine V.toScheme := hV
  let : IsNoetherianRing Γ(U.toScheme, ⊤) :=
    IsLocallyNoetherian.component_noetherian ⟨⊤, isAffineOpen_top U.toScheme⟩
  let aV := (ρ ⁻¹ᵁ V).ι ≫ a
  let ρV := ρ ∣_ V
  let tV := V.ι ≫ t
  have hpV : IsPullback aV ρV A.scheme.hom tV :=
    (isPullback_morphismRestrict ρ V).flip.paste_horiz hp
  let k := t.resLE U V hVU
  have hk : k ≫ U.ι = tV := t.resLE_comp_ι hVU
  obtain ⟨b, _, hpb⟩ := CartesianOpenBasePullback.cartesian_open_base_pullback_factor A.scheme.hom aV ρV tV hpV U k hk
  have hf : IsIso ρV.appTop :=
    AffineBaseChangeFunctions.abelian_affine_baseChange_globalFunctions_isIso (A.pullback U.ι) b ρV k hpb
  exact (HilbertConstruction.FunctionSheafAffineCriterion.morphismRestrict_appTop_isIso_iff ρ V).mp hf

end

/-! The direct image of the structure sheaf of an abelian family over
a locally noetherian base remains the actual base structure sheaf on
every base change, including arbitrary nonreduced test schemes. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace

variable {S : Scheme.{0}} [IsLocallyNoetherian S] {g : ℕ} (A : HilbertConstruction.Abelian.Schemes.AbelianScheme g S)
  {Y T : Scheme.{0}} (a : Y ⟶ A.scheme.left) (ρ : Y ⟶ T) (t : T ⟶ S)
  (hp : CategoryTheory.IsPullback a ρ A.scheme.hom t)

include hp in
theorem abelian_baseChange_functionSheaf_isIso : IsIso (HilbertConstruction.FunctionSheafAffineCriterion.functionSheafMap ρ) := by
  let B := Σ U : S.affineOpens, {V : T.affineOpens // V.1 ≤ t ⁻¹ᵁ U.1}
  let O : B → T.Opens := fun i => i.2.1.1
  have hB : Opens.IsBasis (Set.range O) := by
    apply Opens.isBasis_iff_nbhd.mpr
    intro W z hz
    obtain ⟨_, ⟨U, hU, rfl⟩, hzU, _⟩ :=
      S.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ (t z)) isOpen_univ
    obtain ⟨_, ⟨V, hV, rfl⟩, hzV, hVW⟩ :=
      T.isBasis_affineOpens.exists_subset_of_mem_open
        (show z ∈ W ⊓ t ⁻¹ᵁ U from ⟨hz, hzU⟩) (W ⊓ t ⁻¹ᵁ U).isOpen
    exact ⟨V, ⟨⟨⟨U, hU⟩, ⟨⟨V, hV⟩, hVW.trans inf_le_right⟩⟩, rfl⟩,
      hzV, hVW.trans inf_le_left⟩
  apply TopCat.Sheaf.isIso_iff_isIso_basis hB
  intro i
  exact abelian_baseChange_function_app_of_affine_pair A a ρ t hp
    i.1.1 i.1.2 i.2.1.1 i.2.1.2 i.2.2

include hp in
theorem abelian_baseChange_function_app_isIso (V : T.Opens) : IsIso (ρ.app V) := by
  let : IsIso (HilbertConstruction.FunctionSheafAffineCriterion.functionSheafMap ρ) := abelian_baseChange_functionSheaf_isIso A a ρ t hp
  have : IsIso ((TopCat.Sheaf.forget CommRingCat T).map (HilbertConstruction.FunctionSheafAffineCriterion.functionSheafMap ρ)) :=
    (TopCat.Sheaf.forget CommRingCat T).map_isIso _
  have : IsIso ρ.c := this
  exact NatIso.isIso_app_of_isIso _ (Opposite.op V)

include hp in
theorem abelian_baseChange_globalFunctions_isIso : IsIso ρ.appTop :=
  abelian_baseChange_function_app_isIso A a ρ t hp ⊤

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Abelian.BaseChangeFunctionSheaf

import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.FiltrationBaseLength

/-! # Filtration Euler -/

namespace OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Flat.FiltrationEuler

noncomputable section

/-! A fixed affine prime filtration computes native Tor Euler
pairings after flat base change. The same filtration can therefore be
used at all native stalks before moving the other intersection cycle. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open _root_.CategoryTheory
open scoped TensorProduct

universe u

variable (R S : Type u) [CommRing R] [CommRing S] [IsNoetherianRing R] [IsNoetherianRing S]
  [Algebra R S] [Module.Flat R S]
  (M : ModuleCat.{u} R) [Module.Finite R M]
  (N : ModuleCat.{u} S) [Module.Finite S N] (d : ℕ) [HasProjectiveDimensionLE N d]
  (p : PrimeSpectrum S)
  (hp : Module.support S ((Extension.baseChange R S).obj M) ∩ Module.support S N ⊆ {p})

include hp in
theorem submodule_step (L K : Submodule R M) (hLK : L ≤ K) :
    Tor.Euler.euler S ((Extension.baseChange R S).obj (.of R K)) N d =
      Tor.Euler.euler S ((Extension.baseChange R S).obj (.of R L)) N d +
      Tor.Euler.euler S ((Extension.baseChange R S).obj (.of R (K ⧸ L.submoduleOf K))) N d := by
  let F := Extension.baseChange R S
  let T := IsolatedTorEuler.submoduleSequence R (.of R K) (L.submoduleOf K)
  have hT := IsolatedTorEuler.submoduleSequence_shortExact R (.of R K) (L.submoduleOf K)
  let : Mono T.f := hT.mono_f
  let : Epi T.g := hT.epi_g
  let i : ModuleCat.of R K ⟶ M := ModuleCat.ofHom K.subtype
  let : Mono i := (ModuleCat.mono_iff_injective i).mpr K.subtype_injective
  have hK : Module.support S (F.obj (.of R K)) ∩ Module.support S N ⊆ {p} :=
    (Set.inter_subset_inter_left _ (Module.support_subset_of_injective (F.map i).hom
      ((ModuleCat.mono_iff_injective _).mp (inferInstance : Mono (F.map i))))).trans hp
  let : Module.Finite S (T.map F).X₂ := by
    change Module.Finite S (S ⊗[R] K)
    infer_instance
  have he := IsolatedTorEuler.additivity S N (T.map F) (hT.map F) d p hK
  change Tor.Euler.euler S (F.obj (.of R K)) N d =
    Tor.Euler.euler S (F.obj (.of R (L.submoduleOf K))) N d +
      Tor.Euler.euler S (F.obj (.of R (K ⧸ L.submoduleOf K))) N d at he
  rw [PrimeFiltrationEuler.euler_iso_left S
    (F.mapIso (Submodule.submoduleOfEquivOfLe hLK).toModuleIso) N d] at he
  exact he

include hp in
theorem filtration_sum
    (s : RelSeries {(L, K) | Submodule.IsQuotientEquivQuotientPrime (A := R) (M := M) L K})
    (h₀ : s.head = ⊥) (ht : s.last = ⊤) :
    Tor.Euler.euler S ((Extension.baseChange R S).obj M) N d =
      ∑ i : Fin s.length, Tor.Euler.euler S ((Extension.baseChange R S).obj
        (.of R (s i.succ ⧸ (s i.castSucc).submoduleOf (s i.succ)))) N d := by
  let F := Extension.baseChange R S
  have hs (n : ℕ) (hn : n < s.length + 1) :
      Tor.Euler.euler S (F.obj (.of R (s ⟨n, hn⟩))) N d =
        ∑ i : Fin n, Tor.Euler.euler S (F.obj
          (.of R (s ⟨i.val + 1, (Nat.succ_le_of_lt i.isLt).trans_lt hn⟩ ⧸
            (s ⟨i.val, i.isLt.trans hn⟩).submoduleOf
              (s ⟨i.val + 1, (Nat.succ_le_of_lt i.isLt).trans_lt hn⟩)))) N d := by
    induction n with
    | zero =>
      change Tor.Euler.euler S (F.obj (.of R s.head)) N d = _
      rw [h₀]
      let : Subsingleton (F.obj (.of R (⊥ : Submodule R M))) := by
        change Subsingleton (S ⊗[R] (⊥ : Submodule R M))
        infer_instance
      rw [PrimeFiltrationEuler.euler_zero_left]
      simp
    | succ n ih =>
      rw [Fin.sum_univ_castSucc, submodule_step R S M N d p hp
        (s ⟨n, by omega⟩) (s ⟨n + 1, hn⟩) (s.step ⟨n, by omega⟩).1, ih (by omega)]
      rfl
  have he := hs s.length (by omega)
  change Tor.Euler.euler S (F.obj (.of R s.last)) N d = _ at he
  rw [ht, PrimeFiltrationEuler.euler_iso_left S
    (F.mapIso (Submodule.topEquiv : (⊤ : Submodule R M) ≃ₗ[R] M).toModuleIso) N d] at he
  exact he

end

end OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Flat.FiltrationEuler
